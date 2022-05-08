"""
General Notes
-------------
This module is an implementation of a modern SAT solver.
This module implement only the building block methods/actions of the solver.
The "solution strategy is implemented in a more general solver DPLLT, which
allows to integrate a theory to the conditions the solver must take into
account. The SAT solver can run without a theory using the DPLL facade of DPLLT.

Preprocess:
The solver preprocess the given formula into a cnf form and map every literal
into an int representation, where -i represent the negation of i. The numeric
representation is then fed into the model as a list of Clauses objects.

Main techniques used by the solver:
1) CDCL (conflict-driven clause learning) -
    This technique provides the solver a way to learn from conflict it gets to
    inorder to avoid similar bad assignments down the search path.
    It does so by creating an implication graph which helps the solver to know
    what each single literal assignment implied so when conflict arrives,
    the solver can detect the "root" of the conflict and mark it as such
    inorder for it to avoid it from that point on.

    More on that subject can be found here:
    https://en.wikipedia.org/wiki/Conflict-driven_clause_learning

2) BCP (boolean constraint propagation, also known as UP/ unit propagation) -
    Experiments suggests that this efficient method usually responsible for
    80-90% of the assignments the solver is making.

    The idea is simple. Since the formula is being preprocessed into a cnf form,
    the formula the solver tries to solve is a conjunction of clauses,
    each is a disjunction of literals. This means that in order for the whole
    formula to be True -> each clause must be True -> at least one of
    the literals in each clause must be True. BCP is looking for clauses where
    all literals are assigned to False bar 1 unassigned literal.
    In that case, the clause and the current partial assignment implies that
    this unassigned literal must be assigned to True.

    The BCP is implemented using watch literals, watchers which are coupled
    to 2 unassigned literals in each clause and alert if the solver's status
    might be relevant for a BCP step. This implementation requires much less
    updates and checks than in a naive implementation.

3) DLIS (dynamic largest individual sum) -
    When there isn't a single literal that its assignment implied from the
    partial assignment of the formula we need to decide which unassigned literal
    to assign first. DLIS is a decision heuristic which directs the
    literal choice to the literal which satisfies as many currently
    unsatisfied clauses as possible. There are more efficient decision methods
    but DLIS is a simple one which provides a glimpse for a non trivial random
    decision.

    For more decision heuristics see
    http://fmv.jku.at/papers/BiereFroehlich-SAT15.pdf
"""

from collections import defaultdict, deque
from typing import Optional, Set, Tuple

from constants import ResultCode, CONFLICT_ID


class Clause:
    def __init__(self, clause: Set[int], clause_index: int):
        self.set_clause = clause
        self.index = clause_index
        self.watch_literals = set()

    def __repr__(self) -> str:
        return repr(self.set_clause)

    def evaluate(self, assignment: Set[int]) -> ResultCode:
        """
        Evaluate the satisfiability statue of the clause for
        the given assignment
        :param assignment: A set of ints representing the assignment
        to evaluate the clause for
        :return: The relevant ResultCode for the situation
        """
        undecided_flag = False
        for int_lit in self.set_clause:
            if int_lit in assignment:
                # Found one True int_lit, since a clause is a Disjunction
                # the clause is SAT
                print("int_lit in assignment:", int_lit)
                return ResultCode.SAT
            elif -int_lit not in assignment:
                undecided_flag = True
        if undecided_flag:
            # There is still at least one int_lit in clause which wasn't
            # assigned. Therefore its satisfiability can't still be determined
            return ResultCode.UNDECIDED
        # All the literals in the clause were assigned to False
        return ResultCode.CONFLICT

    def suggest_watch_literals(self, assignment: Set[int]) -> Set[int]:
        """
        Suggest watch literals given the assignment is the one given as an arg.
        Try to suggest a pair if possible.
        :param assignment: The assignment to suggest watch literals against.
        :return: A set of ints representing the suggested watch literals.
        """
        suggested_wl = set()
        for int_lit in self.set_clause:
            if (int_lit not in assignment) and (-int_lit not in assignment):
                suggested_wl.add(int_lit)
                if len(suggested_wl) == 2:
                    return suggested_wl
        return suggested_wl


class ImplicationNode:
    """
    Node of Implication graph used for backjump
    """
    def __init__(self, int_lit: int, decision_level: int, antecedent: int)\
            -> None:
        self.d_level = decision_level
        self.int_lit = int_lit
        self.antecedent = antecedent


class ImplicationGraph:
    """
    A graph to represent the implication order of assignment done by the
    SAT solver.
    """
    def __init__(self) -> None:
        self.int_lit_to_node = dict()
        self.d_level_to_int_lits = defaultdict(list)

    def __repr__(self) -> str:
        return repr(self.int_lit_to_node)

    def add_node(self, int_lit: int, decision_level: int,
                 antecedent_id: Optional[int])\
            -> None:
        """
        Add implication node to the graph
        :param int_lit: int representing the literal the node represents
        :param decision_level: the decision level of the literal
        :param antecedent_id: The int representing the antecedent's clause id
        this node's assignment was deduced by.
        """
        node = ImplicationNode(int_lit, decision_level, antecedent_id)
        self.int_lit_to_node[int_lit] = node
        self.d_level_to_int_lits[decision_level].append(int_lit)

    def get_absolute_lit_d_level(self, int_lit: int) -> int:
        """
        Gets the decision level of literal given
        :param int_lit: The id of the literal to get its decision level
        :return: The decision level of the given literal
        """
        if int_lit not in self.int_lit_to_node:
            int_lit *= -1
        return self.int_lit_to_node[int_lit].d_level

    def backjump(self, decision_level: int) -> None:
        """
        Backjump to the given decision level. It restores the graph to the state
        it was in that decision level
        :param decision_level: int representing the decision level
        to backjump to.
        """
        for node in list(self.int_lit_to_node.values()):
            if node.d_level > decision_level:
                self.int_lit_to_node.pop(node.int_lit)
        for level in list(self.d_level_to_int_lits):
            if level > decision_level:
                self.d_level_to_int_lits.pop(level)


class Solver:
    def __init__(self):
        self.assignment = None
        self.unsat_clauses = None
        self.int_lits_to_clauses_ids = None
        self.wl_to_clauses = None
        self.bcp_int_lits_queue = None
        self.bcp_clauses_queue = None
        self.clauses = None
        self.d_level = None
        self.Igraph = None

        self.reset()

    def reset(self) -> None:
        self.assignment = set()
        self.unsat_clauses = set()
        self.int_lits_to_clauses_ids = defaultdict(set)
        self.wl_to_clauses = defaultdict(set)
        self.bcp_int_lits_queue = deque()
        self.bcp_clauses_queue = deque()
        self.clauses = []
        self.d_level = 0
        self.Igraph = ImplicationGraph()

    def _len_clause_absolute_lits_at_d_level(self, set_clause: Set[int],
                                             decision_level: int) -> int:
        """
        Get the number of literals which were assigned to either True/False
        at a certain decision level and are part of a certain clause.
        Counts literals which are negations of one another as a single literal
        :param set_clause: A set of ints representing a disjunction of literals
        :param decision_level: Int of the decision level to search for
        :return: Th number of literals meeting the conditions mentioned above
        """
        d_level_int_lits = self.Igraph.d_level_to_int_lits[decision_level]
        absolute_d_level_lits = {abs(lit) for lit in d_level_int_lits}
        absolute_clause_lits = {abs(lit) for lit in set_clause}

        return len(absolute_d_level_lits.intersection(absolute_clause_lits))

    def _get_last_assigned_literal(self, set_clause: Set[int]) -> int:
        """
        Gets the last assigned literal in a clause
        :param set_clause: The clause to be evaluated (represented
        as a set of ints)
        :return: The int representing the last assigned literal in the clause
        """
        print("get_last_assigned_literal for clause:", set_clause)
        int_lits_at_last_d_level = self.Igraph.d_level_to_int_lits[self.d_level]

        print(int_lits_at_last_d_level)
        print(set_clause)

        for int_lit in reversed(int_lits_at_last_d_level):
            if (int_lit in set_clause) or (-int_lit in set_clause):
                print("returning:", int_lit)
                return int_lit

    def _resolve_around_literal(self, set_clause1: Set[int],
                                set_clause2: Set[int],
                                int_lit: int) -> Set[int]:
        """
        Get a resolution for 2 clauses containing a conflict around the given
        literal and its negation needing to coexist.
        :param set_clause1: A set of ints representing a disjunction of literals
        :param set_clause2: A set of ints representing a disjunction of literals
        to confront with clause 1
        :param int_lit: An int representing the literal which the 2 clauses
        have conflict around
        :return: A set of ints representing a resolution clause of the 2 input
        clauses, removing the conflict on the given literal and its negation.
        """
        print("resolving:", set_clause1, set_clause2)

        temp_clause = set_clause1.union(set_clause2)
        temp_clause.discard(int_lit)
        temp_clause.discard(-int_lit)

        print("resolved:", temp_clause)
        return temp_clause

    def _resolve_clauses(self, set_clause1: Set[int], set_clause2: Set[int])\
            -> Set[int]:
        """
        Get a resolution for 2 clauses containing a conflict
        :param set_clause1: A set of ints representing a disjunction of literals
        :param set_clause2: A set of ints representing a disjunction of literals
        to confront with clause 1
        :return: A set of ints representing a resolution clause of the 2 input
        clauses.
        """
        for int_lit in set_clause1:
            if -int_lit in set_clause2:
                return self._resolve_around_literal(set_clause1,
                                                    set_clause2, int_lit)

    def _get_second_highest_d_level(self, set_clause: Set[int]) -> int:
        """
        Get the second highest decision level in a clause
        :param set_clause: The clause to be processed (represented as a
        set of ints)
        :return: The second highest decision level in the clause
        """
        highest_d_level = 0
        second_highest_d_level = 0

        for int_lit in set_clause:
            cur_int_lit_level = self.Igraph.get_absolute_lit_d_level(int_lit)

            if cur_int_lit_level >= highest_d_level:
                second_highest_d_level = highest_d_level
                highest_d_level = cur_int_lit_level

        return second_highest_d_level

    def _set_watch_literals_for_clause(self, clause: Clause,
                                       new_watch_literals: Set[int]) -> None:
        """
        Set watch literals for a clause (for more information about the concept
        of watch literals see the general notes at the beginning of the file).
        :param clause: The clause to set watch literals for
        :param new_watch_literals: The new watch literals to be set for
        the given clause.
        """
        old_watch_literals = clause.watch_literals

        for wl in old_watch_literals:
            self.wl_to_clauses[wl].remove(clause.index)

        clause.watch_literals = new_watch_literals

        for wl in new_watch_literals:
            self.wl_to_clauses[wl].add(clause.index)

    def add_clause(self, set_clause: Set[int]) -> int:
        """
        Add clause to the formula currently solved by the solver
        :param set_clause: The added clause represented as set of ints
        :return: The id of the new clause
        """
        print("Adding clause:", set_clause)

        new_clause_id = len(self.clauses)
        clause = Clause(set_clause, new_clause_id)
        self.clauses.append(clause)

        if not (clause.evaluate(self.assignment) == ResultCode.SAT):
            self.unsat_clauses.add(new_clause_id)
        for int_lit in clause.set_clause:
            self.int_lits_to_clauses_ids[int_lit].add(new_clause_id)
        return new_clause_id

    def assign_literal(self, int_lit: int, antecedent_id: Optional[int])\
            -> None:
        """
        Assign a literal deduced by the clause with id antecedent
        :param int_lit: The int value representing the literal to assign to True
        :param antecedent_id: The int value representing the id clause this
        assignment was deduced by. If This assignment was decided and not
        deduced, expects None value.
        """
        print("Assigning literal:", int_lit)

        self.assignment.add(int_lit)
        self.bcp_int_lits_queue.append(int_lit)

        self.unsat_clauses.difference_update(
            self.int_lits_to_clauses_ids[int_lit])
        self.Igraph.add_node(int_lit, self.d_level, antecedent_id)

    def unassign_literal(self, int_lit: int) -> None:
        """
        Unassign a literal
        :param int_lit: int representing the literal to unassign
        """
        print("Unassigning literal:", int_lit)
        self.assignment.remove(int_lit)

        for clause_id in self.int_lits_to_clauses_ids.get(int_lit):
            clause = self.clauses[clause_id]

            if clause.evaluate(self.assignment) == ResultCode.UNDECIDED:
                self.unsat_clauses.add(clause_id)

    def resolve_conflict(self, initial_set_clause: Set[int])\
            -> Tuple[Set[int], int]:
        """
        Resolve a conflict appeared in initial_clause
        :param initial_set_clause: A clause where the conflict occurred
        (represented as a set of ints, each mapped to a literal)
        :return: Tuple of a new clause to learn from the
        resolution and decision level to backjump to.
        """
        print("resolve_conflict - Igraph:", self.Igraph)
        if initial_set_clause is None:
            cur_clause_id = self.Igraph.int_lit_to_node[CONFLICT_ID].antecedent
            cur_set_clause = self.clauses[cur_clause_id].set_clause
        else:
            cur_set_clause = initial_set_clause

        cur_d_level = self.d_level
        while self._len_clause_absolute_lits_at_d_level(cur_set_clause,
                                                        cur_d_level) > 1:
            last_assigned_int_lit = self._get_last_assigned_literal(
                cur_set_clause)
            last_assigned_node = self.Igraph.int_lit_to_node[
                last_assigned_int_lit]

            print("last_assigned_node:", last_assigned_node)
            antecedent_id = last_assigned_node.antecedent
            antecedent_set_clause = self.clauses[antecedent_id].set_clause
            cur_set_clause = self._resolve_clauses(cur_set_clause,
                                                   antecedent_set_clause)

        return cur_set_clause, self._get_second_highest_d_level(cur_set_clause)

    def backjump(self, new_decision_level: int) -> Set[int]:
        """
        Backjump the solver to a previous decision level. It restores the solver
        to the given decision level unassign later assignments from
        both the assignment set and the implication graph
        :param new_decision_level: The decision level to backjump to
        :return: The new assignment after the backjump
        """
        print("Backjumping to level:", new_decision_level)

        while self.d_level > new_decision_level:
            int_lits_to_unassign = self.Igraph.d_level_to_int_lits[self.d_level]

            for int_lit in int_lits_to_unassign:
                if int_lit in self.assignment:
                    self.unassign_literal(int_lit)

                elif -int_lit in self.assignment:
                    self.unassign_literal(-int_lit)

            self.d_level = self.d_level - 1
        self.Igraph.backjump(new_decision_level)
        return self.assignment

    def has_unsat_clauses(self) -> bool:
        """
        Check if the formula currently solved have clauses which are UNSAT
        :return: True if it does have at least one, False otherwise
        """
        return len(self.unsat_clauses) > 0

    def deduce(self, clause_id: int) -> Tuple[ResultCode, Optional[int]]:
        """
        Try to suggest a deduction of an assignment from the given clause.
        :param clause_id: The id of the clause to look at
        :return: (ResultCode.SAT, suggested_literal) if found a deduction,
                 else return tuple of the clause current ResultCode, None
        """
        clause = self.clauses[clause_id]
        print("clause being deduced is:", clause_id, clause)
        if clause.evaluate(self.assignment) == ResultCode.SAT:
            print("evaluated clause as true")
            return ResultCode.SAT, None

        suggested_wl = clause.suggest_watch_literals(self.assignment)
        if len(suggested_wl) == 0:
            self.Igraph.add_node(CONFLICT_ID, self.d_level, clause_id)
            return ResultCode.CONFLICT, None
        if len(suggested_wl) == 1:
            print("deduce literal:", suggested_wl)
            return ResultCode.SAT, suggested_wl.pop()

        self._set_watch_literals_for_clause(clause, suggested_wl)
        return ResultCode.UNDECIDED, None

    def bcp_step(self) \
            -> Tuple[Optional[ResultCode], Optional[int], Optional[int]]:
        """
        Perform a bcp attempt to deduce an assignment. For more on BCP see
        the general notes at the beginning of the file
        :return: A Tuple of 3 values:
                * ResultCode of the clause tried to be deduced from. None if no
                  clause is a candidate for it.
                * Int representing the suggested assignment if one was
                  suggested. None otherwise
                * clause id of the antecedent clause for the suggested
                 assignment. None if there is no such.
        """
        print("Starting BCP with queue:", self.bcp_int_lits_queue)

        if self.bcp_clauses_queue:
            clause_id = self.bcp_clauses_queue.popleft()
            res_code, suggested_wl = self.deduce(clause_id)
            return res_code, suggested_wl, clause_id

        while self.bcp_int_lits_queue:
            bcp_int_lit = self.bcp_int_lits_queue.popleft()
            self.bcp_clauses_queue.extend(self.wl_to_clauses[-bcp_int_lit])
            if self.bcp_clauses_queue:
                clause_id = self.bcp_clauses_queue.popleft()
                res_code, suggested_wl = self.deduce(clause_id)
                return res_code, suggested_wl, clause_id

        return None, None, None

    def decide(self) -> int:
        """
        Make a decision to which int literal to assign next. Designed to be used
        when there is no assignments applied from the current assignment
        :return: The int value representing the assignment suggested
        """
        print("DSIL picking int literal")
        int_lit_unsat_clause_count = defaultdict(int)
        assignment = self.assignment
        for clause_id in self.unsat_clauses:
            clause = self.clauses[clause_id]

            for int_lit in clause.set_clause:
                if (int_lit not in assignment) and (-int_lit not in assignment):
                    int_lit_unsat_clause_count[int_lit] += 1

        return max(int_lit_unsat_clause_count,
                   key=lambda k: int_lit_unsat_clause_count[k])
