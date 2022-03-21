from __future__ import annotations

import itertools
import networkx as nx

from collections.abc import Iterable
from collections import deque
from typing import List, Union, Set, Dict, Tuple
from constants import ResultCode
from parsing.logical_blocks import Var, Negate, Func, Equal, NEqual, Atom, \
    UnaryOp, BinaryOp
from copy import deepcopy
from theories.PropositionalTheory import PropositionalTheory,\
    PROPOSITIONAL_SUPPORTED_TYPES

LiteralExpression = Union[Func, Var, Negate, Equal, NEqual]

UF_SUPPORTED_TYPES = PROPOSITIONAL_SUPPORTED_TYPES + (Func, Equal, NEqual)


class TheoryState(object):
    def __init__(self, graph: nx.DiGraph, unassigned_vars_ints: Set[int],
                 t_propagations_queue: deque, active_neqs: Set[NEqual]):
        self.graph = graph
        self.unassigned_vars_ints = unassigned_vars_ints
        self.t_propagations_queue = t_propagations_queue
        self.active_neqs = active_neqs


def _unique_expressions_helper(expressions_set: Set[LiteralExpression],
                               cur_expr: LiteralExpression):
    if isinstance(cur_expr, Negate):
        cur_expr = cur_expr.item
    expressions_set.add(cur_expr)
    if isinstance(cur_expr, Func):
        for arg in cur_expr.args:
            _unique_expressions_helper(expressions_set, arg)


def get_unique_terms(abstract_literals: Iterable[LiteralExpression])\
        -> Set[LiteralExpression]:
    expressions = set()
    for abs_lit in abstract_literals:
        if isinstance(abs_lit, (Var, Func, Negate)) and abs_lit.is_literal():
            _unique_expressions_helper(expressions, abs_lit)

        elif isinstance(abs_lit, (Equal, NEqual)):
            left, right = abs_lit.left, abs_lit.right
            _unique_expressions_helper(expressions, left)
            _unique_expressions_helper(expressions, right)

        else:
            raise ValueError("Incompatible type of literal {0}".format(abs_lit))
    return expressions


class CongruenceGraph:
    def __init__(self, abstraction_map):
        self.graph = None
        unique_terms = get_unique_terms(abstraction_map.values())
        self._init_graph(unique_terms)

    def _add_edges(self, edge_origin: LiteralExpression):
        if isinstance(edge_origin, Func):
            for arg in edge_origin.args:
                if arg in self.graph:
                    self.graph.add_edge(edge_origin, arg)
                    self.graph.nodes[arg]["parents"].add(edge_origin)
                    self._add_edges(arg)

    def _set_node_rep(self, node_atom, node_rep):
        nx.set_node_attributes(self.graph, {node_atom: node_rep}, "rep")

    def _init_graph(self, terms: Iterable[LiteralExpression]):
        self.graph = nx.DiGraph()
        nodes_to_add = [(term, {"rep": None, "parents": set()}) for
                        term in terms]
        self.graph.add_nodes_from(nodes_to_add)

        for term in terms:
            self._set_node_rep(node_atom=term, node_rep=term)
            self._add_edges(edge_origin=term)

    def get_rep(self, node_atom):
        if node_atom not in self.graph:
            raise ValueError("node with {0} label doesn't exists in the graph".
                             format(node_atom))

        if self.graph.nodes[node_atom]["rep"] == node_atom:
            return node_atom
        else:
            return self.get_rep(self.graph.nodes[node_atom]["rep"])

    def _merge_terms_classes(self, t1_elem: LiteralExpression,
                             t2_elem: LiteralExpression):
        t1_rep, t2_rep = [self.get_rep(atom) for atom in (t1_elem, t2_elem)]
        if t1_rep == t2_rep:
            return tuple(), tuple()

        t1_rep_parents, t2_rep_parents = [self.graph.nodes[elem]["parents"] for
                                          elem in (t1_rep, t2_rep)]
        t1_rep_parents_old = t1_rep_parents.copy()
        t2_rep_parents_old = t2_rep_parents.copy()
        t2_rep_parents.update(t1_rep_parents)
        t1_rep_parents.clear()

        self._set_node_rep(t1_rep, t2_rep)
        return t1_rep_parents_old, t2_rep_parents_old

    def apply_equality(self, left, right):
        if left not in self.graph or right not in self.graph:
            msg = "at least one of the labels {0}, {1} isn't in the graph"
            raise ValueError(msg.format(left, right))

        l_rep_parents, r_rep_parents = self._merge_terms_classes(left, right)

        for p_left, p_right in itertools.product(l_rep_parents, r_rep_parents):
            left_args_reps = [self.get_rep(arg) for arg in p_left.args]
            right_args_reps = [self.get_rep(arg) for arg in p_right.args]

            are_same_reps = (left_args_reps == right_args_reps)
            are_different_args = (p_left.args != p_right.args)
            are_same_name = (p_left.name == p_right.name)

            # check funcs names are the same and all reps of args are aligned
            if are_same_name and are_same_reps and are_different_args:
                self.apply_equality(p_left, p_right)


class UFTheory(PropositionalTheory):
    def __init__(self):
        super(UFTheory, self).__init__(UF_SUPPORTED_TYPES)
        self.int_to_literal = None

        self.graph = None

        self.unassigned_ints = None
        self.eqs_neqs_ints = None
        self.active_neqs = None

        self.t_propagations_queue = None

        self.cur_assignment = None
        self.assignment_to_state = None
        self.assignments_log = None

    def reset(self):
        self.int_to_literal = None

        self.graph = None

        self.unassigned_ints = None
        self.eqs_neqs_ints = None
        self.active_neqs = None

        self.t_propagations_queue = None

        self.cur_assignment = None
        self.assignment_to_state = None
        self.assignments_log = None

    def _check_eqs_neqs_args_validity(self, formula):
        if isinstance(formula, (Equal, NEqual)):
            left_arg, right_arg = formula.left, formula.right
            if not isinstance(left_arg, Atom) or\
                    not isinstance(right_arg, Atom):

                error_msg = f"In UFTheory both {type(formula)} args must" \
                            f" be atoms. Got " \
                            f"{type(left_arg)}, {type(right_arg)} instead"
                raise ValueError(error_msg)

            all_args_literals = left_arg.is_literal() and right_arg.is_literal()
            any_args_eqs_neqs = any([isinstance(arg, (Equal, NEqual))
                                     for arg in (left_arg, right_arg)])

            if (not all_args_literals) or any_args_eqs_neqs:
                error_msg = f"In UFTheory both {type(formula)} args must" \
                            f" be literals. Got " \
                            f"{type(left_arg)}, {type(right_arg)} instead."

                raise ValueError(error_msg)

        elif isinstance(formula, UnaryOp):
            self._check_eqs_neqs_args_validity(formula.item)

        elif isinstance(formula, BinaryOp):
            self._check_eqs_neqs_args_validity(formula.left)
            self._check_eqs_neqs_args_validity(formula.right)

    def _check_funcs_args_validity(self, formula):
        if isinstance(formula, Func):
            for arg in formula.args:
                if not arg.is_literal():
                    error_msg = f"Functions args must be literals." \
                                f" Got {type(arg)}"
                    raise ValueError(error_msg)

                elif isinstance(arg, (Equal, NEqual)):
                    raise ValueError(f"Functions args can't be {type(arg)}")

                elif isinstance(arg, Func):
                    self._check_funcs_args_validity(arg)

        elif isinstance(formula, UnaryOp):
            self._check_funcs_args_validity(formula.item)

        elif isinstance(formula, BinaryOp):
            self._check_funcs_args_validity(formula.left)
            self._check_funcs_args_validity(formula.right)

    def _check_formula_validity(self, formula):
        self._check_eqs_neqs_args_validity(formula)
        self._check_funcs_args_validity(formula)

    def preprocess(self, formula: Atom):
        super().preprocess(formula)
        self._check_formula_validity(formula)
        return formula

    def _adapt_and_register_map(self, abstraction_map):
        # convert var literal to v = True and Negate(Var) to v != True
        true_var = Var("$True")
        ints_vars = abstraction_map.keys()
        literals = list(abstraction_map.values())

        for i in range(len(literals)):
            cur_val = literals[i]

            if isinstance(cur_val, Var):
                literals[i] = Equal(cur_val, true_var)

            elif isinstance(cur_val, Negate):
                literals[i] = NEqual(cur_val.item, true_var)

        self.int_to_literal = dict(zip(ints_vars, literals))

    def register_abstraction_map(self, abstraction_map: Dict[int, Atom]):
        self._adapt_and_register_map(abstraction_map)

        self.graph = CongruenceGraph(self.int_to_literal)

        self.unassigned_ints = set([abs(literal_int) for literal_int
                                    in self.int_to_literal.keys()])
        self.eqs_neqs_ints = self._get_eqs_neqs_ints()

        self.active_neqs = set()
        self.cur_assignment = []
        self.t_propagations_queue = deque()

        self.assignment_to_state = {tuple(): self._get_cur_state_copy()}
        self.assignments_log = [tuple()]

    def _get_eqs_neqs_ints(self):
        eqs_neqs_ints = set()
        for int_var in self.unassigned_ints:
            cur_lit = self.int_to_literal[int_var]

            if isinstance(cur_lit, (Equal, NEqual)):
                eqs_neqs_ints.add(int_var)
                eqs_neqs_ints.add(-int_var)

        return eqs_neqs_ints

    def _get_cur_state_copy(self):
        return TheoryState(deepcopy(self.graph),
                           deepcopy(self.unassigned_ints),
                           deepcopy(self.t_propagations_queue),
                           deepcopy(self.active_neqs))

    def _restore_properties(self, state: TheoryState,
                            new_assignment: List[int]):
        self.graph = state.graph
        self.unassigned_ints = state.unassigned_vars_ints
        self.t_propagations_queue = state.t_propagations_queue
        self.active_neqs = state.active_neqs
        self.cur_assignment = new_assignment
        self.assignment_to_state[tuple(self.cur_assignment)] = \
            self._get_cur_state_copy()

    def _remove_states_after(self, new_assignment: Tuple[int]):
        remove_from_idx = self.assignments_log.index(new_assignment)
        assignments_to_remove = self.assignments_log[remove_from_idx + 1:]

        for part_assignment in assignments_to_remove:
            # remove key from dict
            self.assignment_to_state.pop(part_assignment, None)
        self.assignments_log = self.assignments_log[:remove_from_idx + 1]

    def _get_active_neqs_reps_paris(self):
        active_neqs_reps_pairs = set()
        for neq in self.active_neqs:
            left_rep = self.graph.get_rep(neq.left)
            right_rep = self.graph.get_rep(neq.right)

            if left_rep != right_rep:
                active_neqs_reps_pairs.add((left_rep, right_rep))
                active_neqs_reps_pairs.add((right_rep, left_rep))
        return active_neqs_reps_pairs

    def _update_t_propagations(self):
        active_neqs_reps_pairs = self._get_active_neqs_reps_paris()

        for int_lit in self.unassigned_ints.intersection(self.eqs_neqs_ints):
            eq_lit = self.int_to_literal[int_lit]
            cur_unassigned_reps = {self.graph.get_rep(x) for x in
                                   (eq_lit.left, eq_lit.right)}

            # check if have the same rep and not yet in propagation queue
            if (len(cur_unassigned_reps) == 1) and (int_lit not in
                                                    self.t_propagations_queue):
                self.t_propagations_queue.append(int_lit)

            # if different reps and there is an unassigned neq between them
            elif (tuple(cur_unassigned_reps) in active_neqs_reps_pairs) and\
                    (-int_lit not in self.t_propagations_queue):
                self.t_propagations_queue.append(-int_lit)

    def _process_eq(self, eq_literal: Equal):
        self.graph.apply_equality(eq_literal.left, eq_literal.right)
        self._update_t_propagations()

    def _process_neq(self, neq_literal: NEqual):
        self.active_neqs.add(neq_literal)
        self._update_t_propagations()

    def _get_conflict_core(self) -> Union[None, Set[int]]:
        problem_core = set()
        last_removed = self.cur_assignment[-1]
        next_assignment_len = len(self.cur_assignment) - 1

        while next_assignment_len >= 0:
            next_assignment = tuple(self.cur_assignment[:next_assignment_len])
            revert_to_state = self.assignment_to_state[next_assignment]
            self._restore_properties(revert_to_state, list(next_assignment))

            for lit_int in problem_core:  # restore problematic literals
                self.process_assignment(lit_int)

            if not self.is_t_conflict():  # -> last removed was part of problem
                problem_core.add(last_removed)

            next_assignment_len -= 1
            last_removed = self.cur_assignment[next_assignment_len]

        return {-lit_int for lit_int in problem_core}

    def process_assignment(self, assignment_int: int):
        self.unassigned_ints.discard(abs(assignment_int))
        self.cur_assignment.append(assignment_int)

        if assignment_int in self.t_propagations_queue:
            self.t_propagations_queue.remove(assignment_int)
        if -assignment_int in self.t_propagations_queue:
            self.t_propagations_queue.remove(-assignment_int)

        abstract_literal = self.int_to_literal[assignment_int]
        if isinstance(abstract_literal, Equal):
            self._process_eq(abstract_literal)
        elif isinstance(abstract_literal, NEqual):
            self._process_neq(abstract_literal)

        cur_assignment = tuple(self.cur_assignment)
        self.assignments_log.append(cur_assignment)
        self.assignment_to_state[cur_assignment] = self._get_cur_state_copy()

    def conflict_recovery(self, new_assignment: Union[List[int], Set[int]]):
        if isinstance(new_assignment, set):
            new_assignment = self.cur_assignment[:len(new_assignment)]
        state_to_revert = self.assignment_to_state[tuple(new_assignment)]

        self._restore_properties(state_to_revert, new_assignment)
        self._remove_states_after(tuple(new_assignment))

    def check_t_propagations(self) -> bool:
        return bool(self.t_propagations_queue)

    def pop_t_propagation(self) -> Union[int, None]:
        if self.t_propagations_queue:
            return self.t_propagations_queue.popleft()
        return None

    def is_t_conflict(self) -> bool:
        for neq in self.active_neqs:
            left_rep = self.graph.get_rep(neq.left)
            right_rep = self.graph.get_rep(neq.right)

            if left_rep == right_rep:
                return True
        return False

    def analyze_satisfiability(self) ->\
            Tuple[ResultCode, Union[None, Set[int]]]:
        if not self.is_t_conflict():
            return ResultCode.SAT, None

        else:
            cur_assignment = self.cur_assignment.copy()
            conflict_core = self._get_conflict_core()
            state_to_revert = self.assignment_to_state[tuple(cur_assignment)]

            self._restore_properties(state_to_revert, cur_assignment)
            self._remove_states_after(tuple(cur_assignment))

            return ResultCode.UNSAT, conflict_core
