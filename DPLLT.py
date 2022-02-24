from __future__ import annotations
from logical_blocks import Atom, Var
from typing import List, Dict
import SATSolver
from constants import ResultCode
from theories.PropositionalTheory import PropositionalTheory
from process_cnf import to_abstract_cnf_conjunction


def _translate_valid_assignment(sat_assignment: List[int],
                                int_to_lit: Dict[int, Atom]):
    valid_assignment = dict()
    for val in sat_assignment:
        cur_literal = int_to_lit[val]
        cur_abs_literal = int_to_lit[abs(val)]
        is_var = isinstance(cur_abs_literal, Var)
        if not (is_var and cur_abs_literal.name.startswith("#")):
            if val > 0:
                valid_assignment[cur_literal] = True
            else:
                valid_assignment[cur_abs_literal] = False
    return valid_assignment


class DPLL:
    def __init__(self):
        self.sat_solver = SATSolver.Solver()
        self.theory = PropositionalTheory()

    def _init_case(self, formula, to_abstract):
        self.original_formula = formula
        self.smt_formula = self.theory.preprocess(formula)
        if to_abstract:
            self.cnf_abstraction, self.abstraction_map = \
                to_abstract_cnf_conjunction(self.smt_formula)
            self.theory.register_abstraction_map(self.abstraction_map)

        else:
            self.cnf_abstraction = self.smt_formula

        self.sat_solver.reset()

    def _register_clauses(self, clauses):
        for clause in clauses:
            clause_id = self.sat_solver.add_clause(clause)
            d_result, suggested_assignment = self.sat_solver.deduce(clause_id)

            if d_result == SATSolver.ResultCode.SAT and\
                    suggested_assignment is not None:
                self._assign_literal(suggested_assignment, clause_id)

            elif d_result == ResultCode.CONFLICT:
                return ResultCode.UNSAT
        return ResultCode.UNDECIDED

    def _assign_literal(self, literal, antecedent):
        self.sat_solver.assign_literal(literal, antecedent)
        self.theory.process_assignment(literal)

    def _handle_conflict(self, start_clause):
        if self.sat_solver.d_level == 0:
            return ResultCode.UNSAT

        new_clause, new_d_level = self.sat_solver.resolve_conflict(start_clause)
        new_partial_assignment = self.sat_solver.backjump(new_d_level)
        self.theory.conflict_recovery(new_partial_assignment)

        learned_cl_id = self.sat_solver.add_clause(new_clause)
        d_result, suggested_assignment = self.sat_solver.deduce(learned_cl_id)

        if d_result == SATSolver.ResultCode.SAT:
            self._assign_literal(suggested_assignment, learned_cl_id)

        return ResultCode.UNDECIDED

    def _confront_with_theory(self, handle_conflict: bool):
        t_result, t_clause = self.theory.analyze_satisfiability()
        if t_result == ResultCode.CONFLICT:
            if handle_conflict:
                if self._handle_conflict(t_clause) == ResultCode.UNSAT:
                    return ResultCode.UNSAT
                else:
                    return ResultCode.CONFLICT
            else:
                return ResultCode.UNSAT
        return ResultCode.SAT

    def _bcp_step(self):
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

    def _perform_bcp(self, handle_conflict: bool):
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

    def solve(self, formula, to_abstract=True):
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
                        literal_to_assign = self.sat_solver.dsil()
                        self.sat_solver.d_level += 1
                        self._assign_literal(literal_to_assign, None)

        return ResultCode.SAT, self.sat_solver.assignment


class DPLLT (DPLL):
    def __init__(self, theory: PropositionalTheory = None):
        super(DPLLT).__init__()
        if theory is not None:
            self.theory = theory

    def solve(self, formula):
        return super().solve(formula, to_abstract=False)
