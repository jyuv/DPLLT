import pytest

from parsing.parse import Parser
from solvers.DPLLT import DPLL


solver = DPLL()
parser = Parser()


def test_eqs_neqs_args_no_errors():
    formula_text = "(a = b) & (y -> (x | (a != c)))"
    formula = parser.parse(formula_text)
    solver.solve(formula)


@pytest.mark.parametrize("formula_text", [
    "((a != b) & (f(x) != y)) | (a = (d | y))",
    "(a != !b) & ((!!c) = d)",
    "a = (a != b)"
])
def test_eqs_neqs_args_errors(formula_text):
    with pytest.raises(ValueError):
        formula = parser.parse(formula_text)
        solver.solve(formula)


@pytest.mark.parametrize("formula_text", [
    "(a = b) & (f(c, d) = g(a))",
    "f(c, !d)"
])
def test_func_args_no_errors(formula_text):
    formula = parser.parse(formula_text)
    solver.solve(formula)


@pytest.mark.parametrize("formula_text", [
    "f(c, d=c)",
    "f(a, f(a, g(d), a | b), c)",
    "f(a, !!c)"
])
def test_func_args_errors(formula_text):
    with pytest.raises(ValueError):
        formula = parser.parse(formula_text)
        solver.solve(formula)
