"""
General Notes
-------------
A set of objects to represent the atoms and to be used by the solvers.

"""

from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Union, Iterable
import numpy as np


class Atom(ABC):
    """
    Abstract basic unit of logical formula
    """

    @abstractmethod
    def is_literal(self) -> bool:
        pass

    @abstractmethod
    def __str__(self) -> str:
        pass

    def __repr__(self) -> str:
        return self.__str__()

    @abstractmethod
    def __eq__(self, other) -> bool:
        pass

    @abstractmethod
    def __hash__(self) -> int:
        pass

    def negate(self) -> Atom:
        """
        Returns the negation of the negation of the Atom
        :return: The negation of the Atom
        """
        raise NotImplementedError


class DualSideLiteral(Atom, ABC):
    """
    Abstract object of literals built of two elements - left and right
    """

    def __init__(self, left, right, symbol: str):
        self.left = left
        self.right = right
        self.symbol = symbol

    def __str__(self) -> str:
        if isinstance(self.left, np.ndarray):
            left_side = repr(self.left)[6:-1]
        else:
            left_side = str(self.left)

        if isinstance(self.left, TYPES_REQUIRE_SEPARATION_LEFT):
            left_side = f"({left_side})"

        if isinstance(self.right, np.ndarray):
            right_side = repr(self.right)[6:-1]
        else:
            right_side = str(self.right)

        if isinstance(self.right, TYPES_REQUIRE_SEPARATION_RIGHT):
            right_side = f"({right_side})"

        return f"{left_side} {self.symbol} {right_side}"

    def __hash__(self) -> int:
        return hash((str(self.left), self.right, self.symbol))

    def __eq__(self, other) -> bool:
        if isinstance(other, type(self)):
            is_same_left = self.left == other.left
            if isinstance(is_same_left, np.ndarray):
                is_same_left = all(is_same_left)

            is_same_right = self.right == other.right
            if isinstance(is_same_right, np.ndarray):
                is_same_right = all(is_same_right)

            return all((is_same_left, is_same_right, self.symbol == other.symbol))
        return False

    def is_literal(self) -> bool:
        return True

    @abstractmethod
    def negate(self) -> Atom:
        pass


class Var(Atom):
    """
    Variable literal
    """

    def __init__(self, name: str, bool_val: Union[str, None] = None):
        self.name = name
        self.bool_val = bool_val

    def assign(self, bool_val):
        self.bool_val = bool_val

    def unassign(self):
        self.bool_val = None

    def is_literal(self) -> bool:
        return True

    def __str__(self) -> str:
        return self.name

    def negate(self) -> Atom:
        return Negate(self)

    def __eq__(self, other) -> bool:
        if isinstance(other, Var):
            return (self.name == other.name) and (self.bool_val == other.bool_val)
        return False

    def __hash__(self) -> int:
        return hash((self.name, self.bool_val))


class Func(Atom):
    """
    Function literal
    """

    def __init__(
        self, name: str, args: Union[Func, Var, Iterable[Union[Func, Var, Negate]]]
    ):
        self.name = name

        if isinstance(args, Iterable):
            self.args = args
        else:
            self.args = [args]

    def __str__(self) -> str:
        args_str = ", ".join([str(arg) for arg in self.args])
        return f"{self.name}({args_str})"

    def __eq__(self, other) -> bool:
        if isinstance(other, Func) and self.name == other.name:
            is_equal_n_args = len(self.args) == len(other.args)
            return is_equal_n_args and (
                all(self.args[i] == other.args[i] for i in range(len(self.args)))
            )
        return False

    def __hash__(self) -> int:
        return hash(tuple([self.name] + list(self.args)))

    def is_literal(self) -> bool:
        return True

    def negate(self) -> Atom:
        return Negate(self)


class Equal(DualSideLiteral):
    """
    Equality literal
    """

    def __init__(self, left, right):
        super(Equal, self).__init__(left, right, symbol="=")

    def negate(self) -> Atom:
        return NEqual(self.left, self.right)


class NEqual(DualSideLiteral):
    """
    Inequality (!=) literal
    """

    def __init__(self, left, right):
        super(NEqual, self).__init__(left, right, symbol="!=")

    def negate(self) -> Atom:
        return Equal(self.left, self.right)


class Geq(DualSideLiteral):
    """
    Greater or Equal (>=) literal
    """

    def __init__(self, left, right):
        super(Geq, self).__init__(left, right, symbol=">=")

    def negate(self) -> Atom:
        return Less(self.left, self.right)


class Less(DualSideLiteral):
    """
    Less literal
    """

    def __init__(self, left, right):
        super(Less, self).__init__(left, right, symbol="<")

    def negate(self) -> Atom:
        return Geq(self.left, self.right)


class LogicalOp(Atom, ABC):
    """
    Abstract object representing logical operations
    """

    pass


class ComplexLogicalOp(LogicalOp, ABC):
    """
    Abstract object representing logical operations which aren't basic
    (basic operations are: Or, And, Negate).
    """

    @abstractmethod
    def to_basic(self) -> Atom:
        """
        Get an equivalent version composed of only basic operations.
        This is very useful for converting formulas to CNF form
        :return: The basic form of the formula
        """
        pass

    def negate(self) -> Atom:
        return self.to_basic().negate()


class UnaryOp(LogicalOp, ABC):
    def __init__(self, item: Atom, symbol: str):
        self.item = item
        self.symbol = symbol

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return self.item == other.item
        return False

    def __hash__(self) -> int:
        return hash((self.item,))

    def __str__(self) -> str:
        if isinstance(self.item, TYPES_REQUIRE_SEPARATION_RIGHT):
            inner_item_rep = f"({self.item})"
        else:
            inner_item_rep = self.item

        return f"{self.symbol}{inner_item_rep}"


class Negate(UnaryOp):
    """
    Negation operator
    """

    def __init__(self, item: Atom):
        super().__init__(item, symbol="!")

    def negate(self) -> Atom:
        return self.item

    def is_literal(self) -> bool:
        return self.item.is_literal() and not isinstance(self.item, Negate)


class BinaryOp(LogicalOp, ABC):
    def __init__(self, left_item: Atom, right_item: Atom, symbol: str):
        self.left = left_item
        self.right = right_item
        self.symbol = symbol

    def is_literal(self) -> bool:
        return False

    def __eq__(self, other) -> bool:
        if isinstance(other, self.__class__):
            return (self.left == other.left) and (self.right == other.right)
        return False

    def __hash__(self) -> int:
        return hash((self.left, self.right))

    def __str__(self) -> str:
        if isinstance(self.left, TYPES_REQUIRE_SEPARATION_LEFT):
            left_side = f"({self.left})"
        else:
            left_side = self.left

        if isinstance(self.right, TYPES_REQUIRE_SEPARATION_RIGHT):
            right_side = f"({self.right})"
        else:
            right_side = self.right

        return f"{left_side} {self.symbol} {right_side}"


class And(BinaryOp):
    """
    And operator
    """

    def __init__(self, left_item: Atom, right_item: Atom):
        super(And, self).__init__(left_item, right_item, symbol="&")

    def negate(self) -> Atom:
        return Or(Negate(self.left), Negate(self.right))


class Or(BinaryOp):
    """
    Or operator
    """

    def __init__(self, left_item: Atom, right_item: Atom):
        super(Or, self).__init__(left_item, right_item, symbol="|")

    def negate(self) -> Atom:
        return And(Negate(self.left), Negate(self.right))

    def cnf_distribute(self) -> Atom:
        """
        Distribute Or operation inwards over Ands:
        replace p | (q & r) with the equivalent (p | q) & (p | r).
        Very useful for CNF transformation

        :return: The distributed version of the formula
        """
        if (isinstance(self.left, And)) and (isinstance(self.right, And)):
            return And(
                Or(self.left.left, self.right.left),
                And(
                    Or(self.left.left, self.right.right),
                    And(
                        Or(self.left.right, self.right.left),
                        Or(self.left.right, self.right.right),
                    ),
                ),
            )
        elif isinstance(self.left, And):
            inner_left, inner_right = self.left.left, self.left.right
            return And(Or(inner_left, self.right), Or(inner_right, self.right))

        elif isinstance(self.right, And):
            inner_left, inner_right = self.right.left, self.right.right
            return And(Or(self.left, inner_left), Or(self.left, inner_right))

        else:
            return self


class Imply(BinaryOp, ComplexLogicalOp):
    """
    Imply operator (left -> right)
    """

    def __init__(self, left_item: Atom, right_item: Atom):
        BinaryOp.__init__(self, left_item, right_item, symbol="->")

    def to_basic(self) -> Atom:
        """
        Get an equivalent version composed of only basic operations.
        This is very useful for converting formulas to CNF form
        :return: The basic form of the formula
        """
        return Or(Negate(self.left), self.right)


class Equiv(BinaryOp):
    """
    Equivalence operator
    """

    def __init__(self, left_item, right_item):
        super(Equiv, self).__init__(left_item, right_item, symbol="<->")

    def to_basic(self) -> Atom:
        """
        Get an equivalent version composed of only basic operations.
        This is very useful for converting formulas to CNF form
        :return: The basic form of the formula
        """
        return And(Or(Negate(self.left), self.right), Or(Negate(self.right), self.left))

    def negate(self) -> Atom:
        return self.to_basic().negate()


TYPES_REQUIRE_SEPARATION_LEFT = (BinaryOp, DualSideLiteral, UnaryOp)
TYPES_REQUIRE_SEPARATION_RIGHT = (BinaryOp, DualSideLiteral)
