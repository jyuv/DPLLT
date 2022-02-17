from collections import defaultdict, deque
from constants import ResultCode, CONFLICT_ID


class Clause:
    def __init__(self, clause, clause_index):
        self.literals = clause
        self.index = clause_index
        self.watch_literals = set()

    def __repr__(self) -> str:
        return repr(self.literals)

    def evaluate(self, assignment):
        undecided_flag = False
        for literal in self.literals:
            if literal in assignment:
                print("literal in assignment:", literal)
                return ResultCode.SAT
            elif -literal not in assignment:
                undecided_flag = True
        if undecided_flag:
            return ResultCode.UNDECIDED
        return ResultCode.CONFLICT

    def suggest_watch_literals(self, assignment):
        suggested_wl = set()
        for literal in self.literals:
            if (literal not in assignment) and (-literal not in assignment):
                suggested_wl.add(literal)
                if len(suggested_wl) == 2:
                    return suggested_wl
        return suggested_wl


class ImplicationNode:
    def __init__(self, literal, decision_level, antecedent):
        self.d_level = decision_level
        self.literal = literal
        self.antecedent = antecedent


class ImplicationGraph:
    def __init__(self):
        self.var_id_to_node = dict()
        self.d_level_to_vars_ids = defaultdict(list)

    def __repr__(self) -> str:
        return repr(self.var_id_to_node)

    def add_node(self, literal, decision_level, antecedent):
        node = ImplicationNode(literal, decision_level, antecedent)
        var_id = abs(literal)
        self.var_id_to_node[var_id] = node
        self.d_level_to_vars_ids[decision_level].append(var_id)

    def get_var_d_level(self, var_id: int):
        return self.var_id_to_node[var_id].d_level

    def backjump(self, decision_level):
        for node in list(self.var_id_to_node.values()):
            if node.d_level > decision_level:
                var_id = abs(node.literal)
                self.var_id_to_node.pop(var_id)
        for level in list(self.d_level_to_vars_ids):
            if level > decision_level:
                self.d_level_to_vars_ids.pop(level)


class Solver:
    def __init__(self):
        self.assignment = None
        self.unsat_clauses = None
        self.literal_to_clauses = None
        self.wl_to_clauses = None
        self.bcp_literals_queue = None
        self.bcp_clauses_queue = None
        self.clauses = None
        self.d_level = None
        self.Igraph = None

        self.reset()

    def reset(self):
        self.assignment = set()
        self.unsat_clauses = set()
        self.literal_to_clauses = defaultdict(set)
        self.wl_to_clauses = defaultdict(set)
        self.bcp_literals_queue = deque()
        self.bcp_clauses_queue = deque()
        self.clauses = []
        self.d_level = 0
        self.Igraph = ImplicationGraph()

    def _clause_vars_at_d_level(self, cur_clause, decision_level):
        print("clause_variables_at_DL:", decision_level)

        vars_at_decision_level = set()
        for literal in cur_clause:
            var_id = abs(literal)

            if var_id in self.Igraph.var_id_to_node:
                var_d_level = self.Igraph.get_var_d_level(var_id)

                if var_d_level == decision_level:
                    vars_at_decision_level.add(literal)

        return vars_at_decision_level

    def _get_last_assigned_var(self, clause):
        print("get_last_assigned_variable for clause:", clause)
        var_at_last_d_level = self.Igraph.d_level_to_vars_ids[self.d_level]

        print(var_at_last_d_level)
        print(clause)

        for variable in reversed(var_at_last_d_level):
            if (variable in clause) or (-variable in clause):
                print("returning:", variable)
                return variable

    def _resolve_around_literal(self, clause1, clause2, literal):
        print("resolving:", clause1, clause2)

        temp_clause = clause1.union(clause2)
        temp_clause.discard(literal)
        temp_clause.discard(-literal)

        print("resolved:", temp_clause)
        return temp_clause

    def _resolve_clauses(self, clause1, clause2):
        for literal in clause1:
            if -literal in clause2:
                return self._resolve_around_literal(clause1, clause2, literal)

    def _get_second_highest_d_level(self, clause):
        highest_d_level = 0
        second_highest_d_level = 0

        for literal in clause:
            var_id = abs(literal)
            cur_literal_level = self.Igraph.get_var_d_level(var_id)

            if cur_literal_level >= highest_d_level:
                second_highest_d_level = highest_d_level
                highest_d_level = cur_literal_level

        return second_highest_d_level

    def _set_watch_literals_for_clause(self, clause, new_watch_literals):
        old_watch_literals = clause.watch_literals

        for wl in old_watch_literals:
            self.wl_to_clauses[wl].remove(clause.index)

        clause.watch_literals = new_watch_literals

        for wl in new_watch_literals:
            self.wl_to_clauses[wl].add(clause.index)

    def add_clause(self, new_clause):
        print("Adding clause:", new_clause)

        new_clause_id = len(self.clauses)
        clause = Clause(new_clause, new_clause_id)
        self.clauses.append(clause)

        if not (clause.evaluate(self.assignment) == ResultCode.SAT):
            self.unsat_clauses.add(new_clause_id)
        for literal in clause.literals:
            self.literal_to_clauses[literal].add(new_clause_id)
        return new_clause_id

    def assign_literal(self, literal, antecedent):
        print("Assigning literal:", literal)

        self.assignment.add(literal)
        self.bcp_literals_queue.append(literal)

        self.unsat_clauses.difference_update(self.literal_to_clauses[literal])
        self.Igraph.add_node(literal, self.d_level, antecedent)

    def unassign_literal(self, literal):
        print("Unassigning literal:", literal)
        self.assignment.remove(literal)

        for clause_index in self.literal_to_clauses.get(literal):
            clause = self.clauses[clause_index]

            if clause.evaluate(self.assignment) == ResultCode.UNDECIDED:
                self.unsat_clauses.add(clause_index)

    def resolve_conflict(self, initial_clause):
        print("resolve_conflict - Igraph:", self.Igraph)
        if initial_clause is None:

            cur_clause_index = self.Igraph.var_id_to_node[CONFLICT_ID].antecedent
            cur_clause = self.clauses[cur_clause_index].literals
        else:
            cur_clause = initial_clause

        cur_d_level = self.d_level
        while len(self._clause_vars_at_d_level(cur_clause, cur_d_level)) > 1:
            last_assigned_var = self._get_last_assigned_var(cur_clause)
            last_assigned_node = self.Igraph.var_id_to_node[last_assigned_var]

            print("last_assigned_node:", last_assigned_node)
            antecedent_id = last_assigned_node.antecedent
            antecedent_clause = self.clauses[antecedent_id].literals
            cur_clause = self._resolve_clauses(cur_clause, antecedent_clause)

        return cur_clause, self._get_second_highest_d_level(cur_clause)

    def backjump(self, new_decision_level):
        print("Backjumping to level:", new_decision_level)

        while self.d_level > new_decision_level:
            vars_to_unassign = self.Igraph.d_level_to_vars_ids[self.d_level]

            for variable in vars_to_unassign:
                if variable in self.assignment:
                    self.unassign_literal(variable)

                elif -variable in self.assignment:
                    self.unassign_literal(-variable)

            self.d_level = self.d_level - 1
        self.Igraph.backjump(new_decision_level)
        return self.assignment

    def has_unsat_clauses(self):
        return len(self.unsat_clauses) > 0

    def deduce(self, clause_id):
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

    def bcp_step(self):
        print("Starting BCP with queue:", self.bcp_literals_queue)

        if self.bcp_clauses_queue:
            clause_id = self.bcp_clauses_queue.popleft()
            return *self.deduce(clause_id), clause_id

        while self.bcp_literals_queue:
            bcp_literal = self.bcp_literals_queue.popleft()
            self.bcp_clauses_queue.extend(self.wl_to_clauses[-bcp_literal])
            if self.bcp_clauses_queue:
                clause_id = self.bcp_clauses_queue.popleft()
                return *self.deduce(clause_id), clause_id

        return None, None, None

    def dsil(self):
        print("DSIL picking literal")
        literal_unsat_clause_count = defaultdict(int)
        assignment = self.assignment
        for clause_index in self.unsat_clauses:
            clause = self.clauses[clause_index]

            for literal in clause.literals:
                if (literal not in assignment) and (-literal not in assignment):
                    literal_unsat_clause_count[literal] += 1

        return max(literal_unsat_clause_count,
                   key=lambda k: literal_unsat_clause_count[k])
