from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Union, Iterable
import numpy as np


class Atom(ABC):
    @abstractmethod
    def is_literal(self) -> bool:
        pass

    @abstractmethod
    def __str__(self):
        pass

    def __repr__(self):
        return self.__str__()

    @abstractmethod
    def __eq__(self, other):
        pass

    @abstractmethod
    def __hash__(self):
        pass

    def negate(self):
        raise NotImplementedError

# Todo: Decide if Inequalities should have general left, right or a, b
# Todo: Choose what to do with __hash__ as far of different types


class InequalityAtom(Atom, ABC):
    def __init__(self, a: np.ndarray, b: int, symbol: str):
        self.a = a
        self.b = b
        self.symbol = symbol

    def __eq__(self, other):
        if isinstance(other, type(self)):
            return (all(self.a == other.a)) and (self.b == other.b)
        return False

    def __hash__(self):
        return hash((str(self.a), self.b))

    def __str__(self):
        if isinstance(self.a, TYPES_REQUIRE_SEPARATION_LEFT):
            left_side = f"({self.a})"
        else:
            left_side = self.a

        if isinstance(self.b, TYPES_REQUIRE_SEPARATION_RIGHT):
            right_side = f"({self.b})"
        else:
            right_side = self.b

        return f"{left_side} {self.symbol} {right_side}"


class Var(Atom):
    def __init__(self, name: str, bool_val: Union[str, None] = None):
        self.name = name
        self.bool_val = bool_val

    def assign(self, bool_val):
        self.bool_val = bool_val

    def unassign(self):
        self.bool_val = None

    def is_literal(self) -> bool:
        return True

    def __str__(self):
        return self.name

    def negate(self):
        raise NotImplementedError

    def __eq__(self, other):
        if isinstance(other, Var):
            return (self.name == other.name) and\
                   (self.bool_val == other.bool_val)
        return False

    def __hash__(self):
        return hash((self.name, self.bool_val))


class Func(Atom):
    def __init__(self, name: str,
                 args: Union[Func, Var, Iterable[Union[Func, Var, Negate]]]):
        self.name = name

        if isinstance(args, Iterable):
            self.args = args
        else:
            self.args = [args]

    def __str__(self):
        args_str = ', '.join([str(arg) for arg in self.args])
        return "{0}({1})".format(self.name, args_str)

    def __eq__(self, other):
        if isinstance(other, Func) and self.name == other.name:
            is_equal_n_args = len(self.args) == len(other.args)
            return is_equal_n_args and (all(self.args[i] == other.args[i]
                                            for i in range(len(self.args))))
        return False

    def __hash__(self):
        return hash(tuple([self.name] + list(self.args)))

    def is_literal(self) -> bool:
        return True

    def negate(self):
        return Negate(self)


# Todo: fix __str__ in Equal and NEqual
class Equal(Atom):
    def __init__(self, left: Atom, right: Atom):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left) + " = " + str(self.right)

    def __eq__(self, other):
        if isinstance(other, Equal):
            return (self.left == other.left) and (self.right == other.right)
        return False

    def __hash__(self):
        if isinstance(self.left, np.ndarray):
            return hash((str(self.left), self.right))
        return hash((self.left, self.right))

    def is_literal(self) -> bool:
        return True

    def negate(self):
        return NEqual(self.left, self.right)


class NEqual(Atom):
    def __init__(self, left: Atom, right: Atom):
        self.left = left
        self.right = right

    def __str__(self):
        return str(self.left) + " != " + str(self.right)

    def __eq__(self, other):
        if isinstance(other, NEqual):
            return (self.left == other.left) and (self.right == other.right)
        return False

    def __hash__(self):
        if isinstance(self.left, np.ndarray):
            return hash((str(self.left), self.right))
        return hash((self.left, self.right))

    def is_literal(self) -> bool:
        return True

    def negate(self):
        return Equal(self.left, self.right)


class Geq(InequalityAtom):
    def __init__(self, a: np.ndarray, b: int):
        super(Geq, self).__init__(a, b, symbol=">=")

    def is_literal(self) -> bool:
        return True

    def negate(self):
        return Less(self.a, self.b)


class Less(InequalityAtom):
    def __init__(self, a: np.ndarray, b: int):
        super(Less, self).__init__(a, b, symbol="<")

    def is_literal(self) -> bool:
        return True

    def negate(self):
        return Geq(self.a, self.b)


class LogicalOp(Atom, ABC):
    pass


class ComplexLogicalOp(LogicalOp, ABC):
    @abstractmethod
    def to_basic(self):
        pass

    def negate(self):
        self.to_basic().negate()


class UnaryOp(LogicalOp, ABC):
    def __init__(self, item: Atom, symbol: str):
        self.item = item
        self.symbol = symbol

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.item == other.item
        return False

    def __hash__(self):
        return hash((self.item, ))

    def __str__(self):
        if self.item.is_literal() or isinstance(self.item, UnaryOp):
            inner_item_rep = self.item
        else:
            inner_item_rep = f"({self.item})"

        return f"{self.symbol}{inner_item_rep}"


class Negate(UnaryOp):
    def __init__(self, item: Atom):
        super().__init__(item, symbol="!")

    def negate(self):
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

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return (self.left == other.left) and (self.right == other.right)
        return False

    def __hash__(self):
        return hash((self.left, self.right))

    def __str__(self):
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
    def __init__(self, left_item: Atom, right_item: Atom):
        super(And, self).__init__(left_item, right_item, symbol="&")

    def negate(self):
        return Or(Negate(self.left), Negate(self.right))


class Or(BinaryOp):
    def __init__(self, left_item: Atom, right_item: Atom):
        super(Or, self).__init__(left_item, right_item, symbol="|")

    def negate(self):
        return And(Negate(self.left), Negate(self.right))

    def cnf_distribute(self):
        if (isinstance(self.left, And)) and (isinstance(self.right, And)):
            return And(Or(self.left.left, self.right.left),
                       And(Or(self.left.left, self.right.right),
                           And(Or(self.left.right, self.right.left),
                               Or(self.left.right, self.right.right))))
        elif isinstance(self.left, And):
            inner_left, inner_right = self.left.left, self.left.right
            return And(Or(inner_left, self.right), Or(inner_right, self.right))

        elif isinstance(self.right, And):
            inner_left, inner_right = self.right.left, self.right.right
            return And(Or(self.left, inner_left), Or(self.left, inner_right))

        else:
            return self


class Imply(BinaryOp, ComplexLogicalOp):
    def __init__(self, left_item: Atom, right_item: Atom):
        BinaryOp.__init__(self, left_item, right_item, symbol="->")

    def to_basic(self):
        return Or(Negate(self.left), self.right)


class Equiv(BinaryOp):
    def __init__(self, left_item, right_item):
        super(Equiv, self).__init__(left_item, right_item, symbol="<->")

    def to_basic(self):
        return And(Or(Negate(self.left), self.right), Or(Negate(self.right),
                                                         self.left))

    def negate(self):
        return self.to_basic().negate()


TYPES_REQUIRE_SEPARATION_LEFT = (BinaryOp, Equal, NEqual, Less, Geq, UnaryOp)
TYPES_REQUIRE_SEPARATION_RIGHT = (BinaryOp, Equal, NEqual, Less, Geq)