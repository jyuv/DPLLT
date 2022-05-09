"""
General Notes
-------------
An implementation of DPLLT (framework for determining satisfiability of SMT
problems (problems which generalize SAT problems to involve additional theory).

The DPLLT is using the lazy approach to combine the theory solver
(which compiles with PropositionalTheory interface) with the SAT solver.

As a simplified facade of the DPLLT a DPLL solver is provided which runs
the SAT solver using CDCL logic.

The solve method of the classes returns a tuple:
    (ResultCode.SAT/UNSAT, assignment)
    The assignment returned is a SAT assignment for SAT code and None for UNSAT.
    The assignment is returned in the form of the original formula provided
    (converting back all the dummy variables).
"""

from __future__ import annotations

from typing import Optional, List, Set, Union, Dict, Tuple

from parsing.logical_blocks import Var, Func, Less, Geq, NEqual, Equal, \
    BinaryOp, UnaryOp, Atom
from solvers import SATSolver
from constants import ResultCode
from solvers.theories.PropositionalTheory import PropositionalTheory
from bool_transforms.process_cnf import to_abstract_cnf_conjunction, \
    to_equalities_with_no_negations_args


class DPLLT:
    def __init__(self, theory: PropositionalTheory = None) -> None:
        self.sat_solver = SATSolver.Solver()
        if theory:
            self.theory = theory
        else:
            self.theory = PropositionalTheory()

    def _init_case(self, formula: Union[List[Set[int]], Atom],
                   to_abstract: bool) -> None:
        """
        Init the solver case to solve
        :param formula: Either the root of logical formula or
        list of sets of ints representing a conjunction of clauses
        :param to_abstract: Boolean of whether to abstract the formula
        (transform to CNF made of ints mapped to the literals in
        the original formula)
        """
        self.original_formula = formula
        if to_abstract:
            self.smt_formula = self.theory.preprocess(formula)
            self.cnf_abstraction, self.abstraction_map, self.dummy_map = \
                to_abstract_cnf_conjunction(self.smt_formula)
            self.theory.register_abstraction_map(self.abstraction_map)

        else:
            self.smt_formula = formula
            self.cnf_abstraction = self.smt_formula

        self.sat_solver.reset()
        self.to_abstract = to_abstract

    def _register_clauses(self, set_clauses: List[Set[int]]) -> ResultCode:
        """
        Register a list of clauses to the SAT solver and try to deduce
        from each one to start building the trivial part of the assignment
        early.
        :param set_clauses: A list of set of ints representing a list of clauses
        to be added
        :return: The ResultCode at the end of the clauses registration (if
        a conflict occured due to the trivial deduction the case is UNSAT
        and the method breaks early.
        """
        for clause in set_clauses:
            clause_id = self.sat_solver.add_clause(clause)
            d_result, suggested_assignment = self.sat_solver.deduce(clause_id)

            if d_result == SATSolver.ResultCode.SAT and\
                    suggested_assignment is not None:
                self._assign_literal(suggested_assignment, clause_id)

            elif d_result == ResultCode.CONFLICT:
                return ResultCode.UNSAT
        return ResultCode.UNDECIDED

    def _assign_literal(self, literal: int, antecedent_id: Optional[int])\
            -> None:
        """
        Updates both SAT solver and theory solver about an assignment
        :param literal: Int representing the literal to be assigned to True
        :param antecedent_id: Int representing the antecedent clause the
        assignment
        was deduced from. None if there is no such clause.
        """
        self.sat_solver.assign_literal(literal, antecedent_id)
        self.theory.process_assignment(literal)

    def _handle_conflict(self, start_set_clause: Optional[Set[int]])\
            -> ResultCode:
        """
        Handle a conflict situation on both SAT solver and theory solver,
        restoring their states and learn a new clause to reduce the searching
        tree.
        :param start_set_clause: A clause causing the conflict if the it's a theory
        conflict. None if the conflict is derived from the SAT solver (in that
        case the conflict is easily derived by the implication graph).
        :return: ResultCode of the solver after the conflict was handled.
        """
        if self.sat_solver.d_level == 0:
            return ResultCode.UNSAT

        new_set_clause, new_d_level = self.sat_solver.resolve_conflict(
            start_set_clause)
        new_partial_assignment = self.sat_solver.backjump(new_d_level)
        self.theory.conflict_recovery(new_partial_assignment)

        learned_cl_id = self.sat_solver.add_clause(new_set_clause)
        d_result, suggested_assignment = self.sat_solver.deduce(learned_cl_id)

        if d_result == SATSolver.ResultCode.SAT:
            self._assign_literal(suggested_assignment, learned_cl_id)

        return ResultCode.UNDECIDED

    def _confront_with_theory(self, handle_conflict: bool) -> ResultCode:
        """
        Confront the solver current state against the theory and
        if handle_conflict try to handle the conflict if such emerge
        :param handle_conflict: Boolean of whether to try to handle
        a conflict if such emerge.
        :return: The ResultCode of the state of the solver against the theory
        when leaving the function.
        """
        t_result, t_clause = self.theory.analyze_satisfiability()
        if t_result == ResultCode.UNSAT:
            if handle_conflict:
                if self._handle_conflict(t_clause) == ResultCode.UNSAT:
                    return ResultCode.UNSAT
                else:
                    return ResultCode.CONFLICT
            else:
                return ResultCode.UNSAT
        return ResultCode.SAT

    def _bcp_step(self) -> ResultCode:
        """
        Perform a single bcp step trying to deduce an assignment from clause.
        :return: The ResultCode of the case after the bcp step.
        """
        d_result, suggested_literal, deduced_from = self.sat_solver.bcp_step()

        if d_result in (ResultCode.SAT, ResultCode.CONFLICT):
            if suggested_literal is not None:
                self._assign_literal(suggested_literal, deduced_from)

        if d_result == ResultCode.SAT:
            if self.sat_solver.has_unsat_clauses():
                return ResultCode.UNDECIDED
            else:
                return ResultCode.SAT

        return d_result

    def _perform_bcp(self, handle_conflict: bool) -> ResultCode:
        """
        Exhaust bcp steps as long as possible
        :param handle_conflict: Boolean value to whether to handle conflict
        if one appears.
        :return: ResultCode at the end
        """
        bcp_step_result = self._bcp_step()
        while bcp_step_result not in (None, ResultCode.SAT,
                                      ResultCode.CONFLICT):
            bcp_step_result = self._bcp_step()

        if bcp_step_result == ResultCode.CONFLICT:
            if handle_conflict:
                if self._handle_conflict(None) == ResultCode.UNSAT:
                    return ResultCode.UNSAT
                else:
                    return ResultCode.CONFLICT
            else:
                return ResultCode.UNSAT

        elif bcp_step_result == ResultCode.SAT:
            return ResultCode.SAT

        return ResultCode.UNDECIDED

    def _replace_dummy_helper(self, atom: Atom) -> Atom:
        """
        Recursive helper function to replace dummy variables
        using self.dummy_map
        :param atom: The root of the formula to currently be processed
        :return: The root of the equivalent processed formula (without dummies)
        """
        if isinstance(atom, Func):
            new_args = []
            for arg in atom.args:
                if arg in self.dummy_map.keys():
                    arg = self.dummy_map[arg]

                elif isinstance(arg, Func):
                    arg = self._replace_dummy_helper(arg)
                new_args.append(arg)
            return Func(atom.name, new_args)

        elif isinstance(atom, (Equal, NEqual, Geq, Less)):
            atom.left = self._replace_dummy_helper(atom.left)
            atom.right = self._replace_dummy_helper(atom.right)

        return atom

    def _get_all_original_equalities_helper(self, formula: Atom,
                                            equalities_set: Set[Equal]) -> None:
        """
        A recursive helper function to extract from the given formula all
        the equalities and equalities which are negations
        of NEquals in the formula, into equalities_set
        :param formula: The root of the logical formula to examine
        :param equalities_set: A set to append equalities found
        """
        if isinstance(formula, BinaryOp):
            self._get_all_original_equalities_helper(formula.left,
                                                     equalities_set)

            self._get_all_original_equalities_helper(formula.right,
                                                     equalities_set)

        elif isinstance(formula, UnaryOp):
            self._get_all_original_equalities_helper(formula.item,
                                                     equalities_set)

        elif isinstance(formula, Func):
            for arg in formula.args:
                if isinstance(arg, Equal):
                    equalities_set.add(arg)
                elif isinstance(arg, NEqual):
                    equalities_set.add(Equal(arg.left, arg.right))
                elif isinstance(arg, Func):
                    self._get_all_original_equalities_helper(arg,
                                                             equalities_set)

        elif isinstance(formula, Equal):
            equalities_set.add(formula)

        elif isinstance(formula, NEqual):
            equalities_set.add(Equal(formula.left, formula.right))

    def _get_all_original_equalities(self):
        """
        Get all the equalities appearing in the original formula and equalities
        which are negations of NEquals in the original formula.
        :return: A set of all original equalities in the original formula
        """
        all_original_equalities = set()
        self._get_all_original_equalities_helper(self.original_formula,
                                                 all_original_equalities)
        return all_original_equalities

    def _assignment_to_original_form(self) -> Dict[Union[Atom, int], bool]:
        """
        Convert the assignment of ints to assignment of logical atoms
        :return: The assignment converted to assignment of the respective
        logical atoms.
        """
        assignment_map = dict()
        cur_assignment = self.sat_solver.assignment

        if self.to_abstract:
            for lit_int in cur_assignment:
                if lit_int > 0:
                    assignment_map[self.abstraction_map[lit_int]] = True
                else:
                    assignment_map[self.abstraction_map[-lit_int]] = False
            assignment_map = self.theory.to_pre_theory_assignment(
                assignment_map)

            # replace to original equalities with negated args
            all_original_equalities = self._get_all_original_equalities()
            for eq in all_original_equalities:
                processed_eq = to_equalities_with_no_negations_args(eq)
                if processed_eq in assignment_map.keys() and eq != processed_eq:
                    assignment_map[eq] = assignment_map[processed_eq]
                    del assignment_map[processed_eq]

            # replace Dummy vars inside functions args
            # (were added because of negations during processing formula)
            pre_replace_lits = list(assignment_map.keys())
            for lit in pre_replace_lits:
                new_lit = self._replace_dummy_helper(lit)
                if new_lit != lit:
                    assignment_map[new_lit] = assignment_map[lit]
                    del assignment_map[lit]

            # remove dummy vars
            pre_replace_lits = list(assignment_map.keys())
            for lit in pre_replace_lits:
                if isinstance(lit, Var) and lit.name.startswith("#"):
                    del assignment_map[lit]

            return assignment_map

        else:
            for lit_int in cur_assignment:
                if lit_int > 0:
                    assignment_map[lit_int] = True
                else:
                    assignment_map[-lit_int] = False
            return assignment_map

    def solve(self, formula: Union[List[Set[int]], Atom],
              to_abstract: bool = True) \
            -> Tuple[ResultCode, Optional[Dict[Union[int, Atom], bool]]]:
        """
        Solve the given formula using this DPLLT solver
        :param formula: Either root of logical formula or list of sets of ints
        representing a conjunction of clauses (CNF form).
        :param to_abstract: boolean of whether to abstract a logical formula
        :return: A tuple of ResultCode, satisfying assignment map in case
        the result is SAT
        """
        self._init_case(formula, to_abstract)

        if self._register_clauses(self.cnf_abstraction) == ResultCode.UNSAT:
            return ResultCode.UNSAT, None

        if self._confront_with_theory(handle_conflict=False) == \
                ResultCode.UNSAT:
            return ResultCode.UNSAT, None

        while self.sat_solver.has_unsat_clauses():
            bcp_result = self._perform_bcp(handle_conflict=True)

            if bcp_result == ResultCode.UNSAT:
                return ResultCode.UNSAT, None

            elif bcp_result == ResultCode.CONFLICT:
                continue

            else:
                t_confront = self._confront_with_theory(handle_conflict=True)
                if t_confront == ResultCode.UNSAT:
                    return ResultCode.UNSAT, None

                elif t_confront == ResultCode.CONFLICT:
                    continue

                elif bcp_result == ResultCode.SAT:
                    break

                elif bcp_result == ResultCode.UNDECIDED:
                    t_propagation = self.theory.pop_t_propagation()
                    if t_propagation is not None:
                        self._assign_literal(t_propagation, None)

                    else:
                        literal_to_assign = self.sat_solver.decide()
                        self.sat_solver.d_level += 1
                        self._assign_literal(literal_to_assign, None)

        original_form_assignment = self._assignment_to_original_form()
        return ResultCode.SAT, original_form_assignment


class DPLL (DPLLT):
    def __init__(self) -> None:
        super(DPLL, self).__init__()

    def solve(self, formula: Union[List[Set[int]], Atom],
              to_abstract: bool = True) \
            -> Tuple[ResultCode, Optional[Dict[Union[int, Atom], bool]]]:
        return super(DPLL, self).solve(formula, to_abstract)
