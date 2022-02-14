from typing import Union
from constants import ResultCode


class PropositionalTheory:
    def preprocess(self, formula):
        return formula

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
