from math import comb
from typing import Union

from constants import ResultCode
from parsing.logical_blocks import Atom, Equal, And, Geq, NEqual, BinaryOp,\
    UnaryOp, Negate, Less
from theories.PropositionalTheory import PropositionalTheory,\
    PROPOSITIONAL_SUPPORTED_TYPES
import numpy as np
from scipy.optimize import linprog


TQ_SUPPORTED_TYPES = PROPOSITIONAL_SUPPORTED_TYPES + (Equal, NEqual, Less, Geq)

UNBOUNDED_STATUS = 3


def scipy_max_simplex(a, b, c):
    max_dim, min_dim = max(*a.shape), min(a.shape)
    options = {'maxiter': comb(max_dim + min_dim, min_dim)}
    return linprog(A_ub=a, b_ub=b, c=-c, options=options,
                   method="highs")


def _convert_equality(equality: Equal):
    # ax=b <-> [(ax >= b) & (-ax >= -b)]
    return And(Geq(equality.left, equality.right),
               Geq(-equality.left, -equality.right))


def _convert_inequality(inequality: NEqual):
    # ax!=b <-> ![(ax >= b) & (-ax >= -b)]
    return Negate(And(Geq(inequality.left, inequality.right),
                      Geq(-inequality.left, -inequality.right)))


class TQTheory(PropositionalTheory):
    def __init__(self, support_negative_vars=True):
        super(TQTheory, self).__init__(TQ_SUPPORTED_TYPES)
        self.assignment = None
        self.A = None
        self.b = None
        self.simplex = scipy_max_simplex
        self.abstraction_map = None
        self.support_negative_vars = support_negative_vars
        self.reset()

    def reset(self):
        self.assignment = set()
        self.A = None
        self.b = None
        self.simplex = scipy_max_simplex
        self.abstraction_map = None
        self.support_negative_vars = self.support_negative_vars

    def register_abstraction_map(self, abstraction_map):
        self.reset()
        self.abstraction_map = abstraction_map

    def _preprocess_helper(self, tq_formula: Atom):
        if isinstance(tq_formula, Equal):
            # ax=b <-> [(ax >= b) & (-ax >= -b)]
            return _convert_equality(tq_formula)
        elif isinstance(tq_formula, NEqual):
            # ax!=b <-> !(the expr above)
            return _convert_inequality(tq_formula)

        elif isinstance(tq_formula, Negate) and isinstance(tq_formula.item,
                                                           Equal):
            return _convert_inequality(tq_formula.item.negate())

        elif isinstance(tq_formula, Negate) and isinstance(tq_formula.item,
                                                           NEqual):
            return _convert_equality(tq_formula.item.negate())

        if not tq_formula.is_literal():
            if isinstance(tq_formula, BinaryOp):
                tq_formula.left = self._preprocess_helper(tq_formula.left)
                tq_formula.right = self._preprocess_helper(tq_formula.right)

            elif isinstance(tq_formula, UnaryOp):
                tq_formula.item = self._preprocess_helper(tq_formula.item)

        return tq_formula

    def _check_args_validity(self, formula: Atom):
        if isinstance(formula, BinaryOp):
            self._check_args_validity(formula.left)
            self._check_args_validity(formula.right)

        elif isinstance(formula, UnaryOp):
            self._check_args_validity(formula.item)

        elif isinstance(formula, (Less, Geq, Equal, NEqual)):
            if not isinstance(formula.left, np.ndarray) or\
                    not isinstance(formula.right, int):
                left_type, right_type = type(formula.left), type(formula.right)
                error_msg = f"Types or atom arguments should be np.ndarray," \
                            f" int. Got {left_type}, {right_type} instead"
                raise ValueError(error_msg)

    def preprocess(self, tq_formula: Atom):
        super().preprocess(tq_formula)
        self._check_args_validity(tq_formula)
        return self._preprocess_helper(tq_formula)

    def _translate_unconstrained_to_standard(self, a):
        # if so each x_i will be represented as x_i+ - x_i-
        if self.support_negative_vars:
            return np.dstack((a, -a)).flatten()
        return a

    def _handle_Geq_update(self, lp_formula):
        # we have a*x >= b <=> -a*x <= -b
        # the last 0 is because there is no y here.
        a = self._translate_unconstrained_to_standard(lp_formula.left)
        if self.A is None:
            self.A = np.hstack((-a, 0)).reshape((1, -1))
            self.b = np.array([-lp_formula.right]).reshape((1, -1))
        else:
            self.A = np.vstack((self.A, np.hstack((-a, 0))))
            self.b = np.vstack((self.b, -lp_formula.right))

    def _handle_Less_update(self, lp_formula):
        # we have a*x < b <=> a*x + y <= b AND y > 0
        a = self._translate_unconstrained_to_standard(lp_formula.left)
        if self.A is None:
            self.A = np.hstack((a, 1)).reshape((1, -1))
            self.b = np.array([lp_formula.right]).reshape((1, -1))
        else:
            self.A = np.vstack((self.A, np.hstack((a, 1))))
            self.b = np.vstack((self.b, lp_formula.right))

    def _update_A_and_b(self, lp_formula):
        if isinstance(lp_formula, Geq):
            self._handle_Geq_update(lp_formula)

        elif isinstance(lp_formula, Less):
            self._handle_Less_update(lp_formula)

    def process_assignment(self, literal):
        self.assignment.add(literal)
        lp_formula = self.abstraction_map.get(literal)
        self._update_A_and_b(lp_formula)

    def conflict_recovery(self, new_assignment):
        self.assignment = set(new_assignment)
        self.A = None
        self.b = None
        for literal in self.assignment:
            lp_formula = self.abstraction_map.get(literal)
            self._update_A_and_b(lp_formula)

    def analyze_satisfiability(self) -> (ResultCode, Union[None, int]):
        if self.A is None:
            return ResultCode.SAT, None

        if any(self.A[:, -1] == 1):  # Does A's last column has a 1
            # taking care of y and change its position
            c = np.zeros(self.A.shape[1])
            c[-1] = 1

            res = self.simplex(self.A, self.b, c)

            # it solved a minimization problem with c=-c
            is_finite_positive_y = res.success and (res.fun < 0)
            is_sat = is_finite_positive_y or (res.status == UNBOUNDED_STATUS)

        else:
            c = np.zeros(self.A.shape[1] - 1)
            res = self.simplex(self.A[:, :-1], self.b, c)
            is_sat = res.success or (res.status == UNBOUNDED_STATUS)

        if is_sat:
            return ResultCode.SAT, None

        else:
            conflict_clause = set()
            for literal in self.assignment:
                conflict_clause.add(-literal)
            return ResultCode.UNSAT, conflict_clause

    def pop_t_propagation(self):
        return None
