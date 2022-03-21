from abc import abstractmethod
from typing import Union, Set, Tuple, Dict
from constants import ResultCode
from parsing.logical_blocks import UnaryOp, BinaryOp, Atom, Var, And, Or,\
    Imply, Equiv, Negate

PROPOSITIONAL_SUPPORTED_TYPES = (Var, And, Or, Imply, Equiv, Negate)


class PropositionalTheory:
    def __init__(self, allowed_atoms_types: Tuple[type, ...] =
                 PROPOSITIONAL_SUPPORTED_TYPES):
        self.allowed_atoms_types = allowed_atoms_types

    @abstractmethod
    def preprocess(self, formula: Atom):
        self._check_atom_types_validity(formula)
        return formula

    def _check_atom_types_validity(self, formula: Atom):
        if not isinstance(formula, self.allowed_atoms_types):
            raise ValueError(f"{type(formula)} is not supported by theory")
        elif isinstance(formula, BinaryOp):
            self._check_atom_types_validity(formula.left)
            self._check_atom_types_validity(formula.right)
        elif isinstance(formula, UnaryOp):
            self._check_atom_types_validity(formula.item)

    @abstractmethod
    def register_abstraction_map(self, abstraction_map):
        pass

    @abstractmethod
    def process_assignment(self, literal):
        pass

    @abstractmethod
    def analyze_satisfiability(self) -> (ResultCode, Union[None, Set[int]]):
        return ResultCode.SAT, None

    @abstractmethod
    def pop_t_propagation(self):
        return None

    @abstractmethod
    def conflict_recovery(self, assignment):
        pass

    @abstractmethod
    def reset(self):
        pass

    @abstractmethod
    def to_pre_theory_assignment(self, assignment_map: Dict[Atom, bool]):
        return assignment_map

