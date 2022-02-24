import pytest

from parse import Parser
from DPLLT import DPLL

str_eqs_neqs_args1 = "(a = b) & (y -> (x | (a != c)))"
str_eqs_neqs_args2 = "((a != b) & (f(x) != y)) | (a = (d | y))"
str_eqs_neqs_args3 = "(a != !b) & ((!!c) = d)"
str_eqs_neqs_args4 = "a = (a != b)"

str_func_args1 = "(a = b) & (f(c, d) = g(a))"
str_func_args2 = "f(c, !d)"
str_func_args3 = "f(c, d=c)"
str_func_args4 = "f(a, f(a, g(d), a | b), c)"
str_func_args5 = "f(a, !!c)"

solver = DPLL()


def test_eqs_neqs_args1():  # Expect no error raised
    formula = Parser(str_eqs_neqs_args1).parse()
    solver.solve(formula)


def test_eqs_neqs_args2():
    with pytest.raises(ValueError):
        formula = Parser(str_eqs_neqs_args2).parse()
        solver.solve(formula)


def test_eqs_neqs_args3():
    with pytest.raises(ValueError):
        formula = Parser(str_eqs_neqs_args3).parse()
        solver.solve(formula)


def test_eqs_neqs_args4():
    with pytest.raises(ValueError):
        formula = Parser(str_eqs_neqs_args4).parse()
        solver.solve(formula)


def test_func_args1():
    formula = Parser(str_func_args1).parse()
    solver.solve(formula)


def test_func_args2():
    formula = Parser(str_func_args2).parse()
    solver.solve(formula)


def test_func_args3():
    with pytest.raises(ValueError):
        formula = Parser(str_func_args3).parse()
        solver.solve(formula)


def test_func_args4():
    with pytest.raises(ValueError):
        formula = Parser(str_func_args4).parse()
        solver.solve(formula)


def test_func_args5():
    with pytest.raises(ValueError):
        formula = Parser(str_func_args5).parse()
        solver.solve(formula)
