from enum import Enum


class ResultCode(Enum):
    SAT = 1
    UNSAT = 2
    UNDECIDED = 3
    CONFLICT = 4


CONFLICT_ID = 0
