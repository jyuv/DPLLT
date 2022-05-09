"""
General Notes
-------------
The most basic theory to be used in the DPLLT solver. This theory doesn't
add requirements to the regular SAT solver bar allowing to restrict the atoms
types. This theory also serves as a interface for other theories APIs.
"""

from abc import abstractmethod
from typing import Union, Set, Tuple, Dict
from constants import ResultCode
from parsing.logical_blocks import (
    UnaryOp,
    BinaryOp,
    Atom,
    Var,
    And,
    Or,
    Imply,
    Equiv,
    Negate,
)

PROPOSITIONAL_SUPPORTED_TYPES = (Var, And, Or, Imply, Equiv, Negate)


class PropositionalTheory:
    def __init__(
        self, allowed_atoms_types: Tuple[type, ...] = PROPOSITIONAL_SUPPORTED_TYPES
    ):
        self.allowed_atoms_types = allowed_atoms_types

    @abstractmethod
    def preprocess(self, formula: Atom) -> Atom:
        """
        Called by the DPLLT solver to adapt the formula to the theory.
        :param formula: formula to adapt
        :return: the adapted formula after preprocess
        """
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
    def register_abstraction_map(self, abstraction_map: Dict[int, Atom]) -> None:
        """
        Registers the abstraction map from int to actual literal object.
        This helps the theory to interpret the int value assignments
        :param abstraction_map: a dictionary mapping int to respective atom
                                literal
        """
        pass

    @abstractmethod
    def process_assignment(self, int_literal: int) -> None:
        """
        Process assignment of a literal by the theory
        :param int_literal: an int value representing an atom literal
        """
        pass

    @abstractmethod
    def analyze_satisfiability(self) -> (ResultCode, Union[None, Set[int]]):
        """
        Checks if the current situation is contradicts with the theory or not.
        :return: if contradicts returns (ResultCode.UNSAT, conflict_clause)
                 else returns (ResultCode.SAT, None)
        """
        return ResultCode.SAT, None

    @abstractmethod
    def pop_t_propagation(self) -> Union[int, None]:
        """
        Pops theory propagation suggestion if one exists for the current state.
        :return: int value representing the suggested literal if propagation
                 exists, None otherwise.
        """
        return None

    @abstractmethod
    def conflict_recovery(self, assignment: Set[int]) -> None:
        """
        Recovers the theory to the state where its assignment is the given
        assignment
        :param assignment: an assignment to recover the state to
        """
        pass

    @abstractmethod
    def reset(self) -> None:
        """
        Resets the theory object
        """
        pass

    @abstractmethod
    def to_pre_theory_assignment(
        self, assignment_map: Dict[Atom, bool]
    ) -> Dict[Atom, bool]:
        """
        Converts the assignment map given into an assignment map which its
        literals are in their pre theory processing form.
        :param assignment_map: assignment map (atom -> bool) to convert
        :return: the converted assignment map
        """
        return assignment_map
