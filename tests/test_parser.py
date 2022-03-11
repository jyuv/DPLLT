import pytest

from logical_blocks import *
from parse import Parser

X, Y = Var("X"), Var("Y")

a = Var("a")
neg_a = Negate(a)
b = Var("b")
neg_b = Negate(b)
c = Var("c")
neg_c = Negate(c)
r = Var("r")
neg_r = Negate(r)
u = Var("u")
neg_u = Negate(u)
v = Var("v")
neg_v = Negate(v)
e = Var("e")
neg_e = Negate(e)
m = Var("m")
neg_m = Negate(m)
n = Var("n")
neg_n = Negate(n)
x = Var("x")
neg_x = Negate(x)
y = Var("y")
neg_y = Negate(y)

eq0_text = "(a & b) | ((!a) & (c -> b))"
eq0 = Or(And(a, b), And(neg_a, Imply(c, b)))


eq1_text = "(((a|(!b))|(r&(!a)))&((c&r)|(c->((!r)&b))))&(((n->a)&((!r)|n))" \
           "->((r&n)&(a|(!n))))"
eq1 = And(
    And(
        Or(
            Or(a, neg_b),
            And(r, neg_a)
        ),
        Or(
            And(c, r),
            Imply(c, And(neg_r, b))
        )
    ),
    Imply(
        And(
            Imply(n, a),
            Or(neg_r, n)
        ),
        And(
            And(r, n),
            Or(a, neg_n)
        )
    )
)

eq2_text = "({0}) & (({1}) -> (n & ((r & a) | !b)))".format(eq0_text, eq1_text)
eq2 = And(eq0, Imply(eq1, And(n, Or(And(r, a), neg_b))))

eq3_text = "({0}) -> (({1}) -> ({2}))".format(eq2_text, eq0_text, eq1_text)
eq3 = Imply(eq2, Imply(eq0, eq1))

eq4_text = "(!({0})) & ({1})".format(eq1_text, eq3_text)
eq4 = And(Negate(eq1), eq3)

ineq1_text = "[5,3,-2,1] < 4"
ineq1 = Less(np.array([5, 3, -2, 1]), 4)
ineq2_text = "[5,3,-2,1] >= 4"
ineq2 = Geq(np.array([5, 3, -2, 1]), 4)
ineq3_text = "[,] < 4"
ineq4_text = "[1,-12a3] < 4"
ineq5_text = "[] < 5"
ineq6_text = "[1] < [2]"

ineq7_text = "([1, 3] < 5) & (a | b)"
ineq7 = And(Less(np.array([1, 3]), 5), Or(a, b))

parser = Parser()


def test1():
    text = "((!X)&Y)|f(X,Y)"
    expected_result = Or(And(Negate(X), Y), Func("f", (X, Y)))
    assert parser.parse(text) == expected_result


def test2():
    text = "a & (!a)"
    expected_result = And(a, neg_a)
    assert parser.parse(text) == expected_result


def test3():
    text = "a | !b"
    expected_result = Or(a, neg_b)
    assert parser.parse(text) == expected_result


def test4():
    text = "!!b"
    expected_result = Negate(neg_b)
    assert parser.parse(text) == expected_result


def test_empty():
    assert parser.parse("") == []


def test_eq0():
    assert parser.parse(eq0_text) == eq0


def test_eq1():
    assert parser.parse(eq1_text) == eq1


def test_eq2():
    assert parser.parse(eq2_text) == eq2


def test_eq3():
    assert parser.parse(eq3_text) == eq3


def test_eq4():
    assert parser.parse(eq4_text) == eq4


def test_array1():
    assert parser.parse(ineq1_text) == ineq1


def test_array2():
    assert parser.parse(ineq2_text) == ineq2


def test_array3():
    with pytest.raises(ValueError):
        parser.parse(ineq3_text)


def test_array4():
    with pytest.raises(ValueError):
        parser.parse(ineq4_text)


def test_array5():
    with pytest.raises(ValueError):
        parser.parse(ineq5_text)


def test_array6():
    with pytest.raises(ValueError):
        parser.parse(ineq6_text)


def test_array7():
    assert parser.parse(ineq7_text) == ineq7

