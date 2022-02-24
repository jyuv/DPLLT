from typing import Union
from constants import ResultCode
from logical_blocks import NEqual, Equal, UnaryOp, BinaryOp, Func


class PropositionalTheory:
    def preprocess(self, formula):
        self._check_eqs_neqs_args_validity(formula)
        self._check_funcs_args_validity(formula)
        return formula

    def _check_eqs_neqs_args_validity(self, formula):
        if isinstance(formula, Equal) or isinstance(formula, NEqual):
            left_arg, right_arg = formula.left, formula.right
            all_args_literals = left_arg.is_literal() and right_arg.is_literal()
            any_args_eqs_neqs = any([isinstance(arg, Equal) or
                                     isinstance(arg, NEqual)
                                     for arg in (left_arg, right_arg)])

            if (not all_args_literals) or any_args_eqs_neqs:
                raise ValueError("Arguments of Equal/NEqual must be literals")
        elif isinstance(formula, UnaryOp):
            self._check_eqs_neqs_args_validity(formula.item)
        elif isinstance(formula, BinaryOp):
            self._check_eqs_neqs_args_validity(formula.left)
            self._check_eqs_neqs_args_validity(formula.right)

    def _check_funcs_args_validity(self, formula):
        if isinstance(formula, Func):
            all_args_literals = all([arg.is_literal() for arg in formula.args])
            any_args_eqs_neqs = any([isinstance(arg, Equal) or
                                     isinstance(arg, NEqual)
                                     for arg in formula.args])

            if (not all_args_literals) or any_args_eqs_neqs:
                raise ValueError("Arguments of functions must be literals")
        elif isinstance(formula, UnaryOp):
            self._check_funcs_args_validity(formula.item)
        elif isinstance(formula, BinaryOp):
            self._check_funcs_args_validity(formula.left)
            self._check_funcs_args_validity(formula.right)

    def register_abstraction_map(self, abstraction_map):
        pass

    def process_assignment(self, literal):
        pass

    def analyze_satisfiability(self) -> (ResultCode, Union[None, int]):
        return ResultCode.SAT, None

    def pop_t_propagation(self):
        return None

    def conflict_recovery(self, assignment):
        pass
