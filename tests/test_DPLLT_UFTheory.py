import pytest

from solvers.DPLLT import DPLLT
from constants import ResultCode
from parsing.parse import Parser
from tests.test_utils import verify_unabstracted_assignment
from theories.UFTheory import UFTheory


str_uf1 = "(g(a) = c) & (((f(g(a)) != f(c)) | (g(a) = d)) & (c != d))"

clauses_strs_uf2 = ["a = b",
                    "(a != b) | ((s != t) | (b = c))",
                    "(s = t) | ((t != r) | (f(s) = f(a)))",
                    "(b != c) | ((t != r) | (f(s) = f(a)))",
                    "(f(s) != f(a)) | (f(a) != f(c))"]
str_uf2 = "({0}) & (({1}) & (({2}) & (({3}) & ({4}))))".format(
    *clauses_strs_uf2)

str_uf3 = "(f(f(f(a))) = a) & ((f(f(f(f(f(a))))) = a) & (f(a) != a))"

clauses_strs_uf4 = ["(a = b) | (g(f(b)) != f(c))",
                    "(c != d) | ((h(h(h(a))) = h(a)) | (f(b) = h(p(a,b))))",
                    "(f(a) = c) | ((f(b) = f(f(g(h(d))))) | (a = c))",
                    "(e = r) | (s = a)",
                    "m(e, r) = m(a, b)",
                    "f(a) != g(h(m(a, r)))",
                    "m(e, r) = m(r, e)",
                    "(g(h(d)) != f(b)) | (g(h(m(r, a))) = f(b))",
                    "f(f(f(b))) = f(b)",
                    "g(h(m(r, a))) != h(p(a, b))",
                    "h(a) = e",
                    "h(e) = r",
                    "h(r) = b",
                    "e != b",
                    "p(a, b) = r",
                    "f(b) != f(f(b))",
                    "f(a) = c",
                    "f(b) = d"]


str_uf4 = "({0}) & (({1}) & (({2}) & (({3}) & (({4}) & (({5}) & (({6})" \
          " & (({7}) & (({8}) & (({9}) & (({10}) & (({11}) & (({12}) & " \
          "(({13}) & (({14}) & (({15}) &" \
          " ((({16}) & ({17}))))))))))))))))))".format(*clauses_strs_uf4)


uf_theory = UFTheory()
solver = DPLLT(uf_theory)
parser = Parser()


@pytest.mark.parametrize("formula_text, expected_result_code", [
    (str_uf1, ResultCode.UNSAT),
    (str_uf2, ResultCode.SAT),
    (str_uf3, ResultCode.UNSAT),
    (str_uf4, ResultCode.SAT)
])
def test_dpllt_with_uf(formula_text, expected_result_code):
    formula = parser.parse(formula_text)
    result_code, assignment = solver.solve(formula)

    assert result_code == expected_result_code
    if expected_result_code == ResultCode.SAT:
        assert verify_unabstracted_assignment(formula, assignment)


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
