from DPLLT import DPLLT
from constants import ResultCode
from parse import Parser
from theories.UFTheory import UFTheory


str_uf1 = "(g(a) = c) & (((f(g(a)) != f(c)) | (g(a) = d)) & (c != d))"

cls_strs_uf2 = ["a = b",
                "(a != b) | ((s != t) | (b = c))",
                "(s = t) | ((t != r) | (f(s) = f(a)))",
                "(b != c) | ((t != r) | (f(s) = f(a)))",
                "(f(s) != f(a)) | (f(a) != f(c))"]
str_uf2 = "({0}) & (({1}) & (({2}) & (({3}) & ({4}))))".format(*cls_strs_uf2)

str_uf3 = "(f(f(f(a))) = a) & ((f(f(f(f(f(a))))) = a) & (f(a) != a))"

cls_strs_uf4 = ["(a = b) | (g(f(b)) != f(c))",
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
          " ((({16}) & ({17}))))))))))))))))))".format(*cls_strs_uf4)


uf_theory = UFTheory()
solver = DPLLT(uf_theory)
parser = Parser()


def test_uf1():
    formula = parser.parse(str_uf1)
    assert solver.solve(formula)[0] == ResultCode.UNSAT


def test_uf2():
    formula = parser.parse(str_uf2)
    assert solver.solve(formula)[0] == ResultCode.SAT


def test_uf3():
    formula = parser.parse(str_uf3)
    assert solver.solve(formula)[0] == ResultCode.UNSAT


def test_uf4():
    formula = parser.parse(str_uf4)
    assert solver.solve(formula)[0] == ResultCode.SAT
