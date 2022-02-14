from bool_transforms import _get_tseitin_equivs, to_nnf, to_cnf
from logical_blocks import Var, Or, And, Negate, Equiv, Imply

x1 = Var("X1")
x2 = Var("X2")
x3 = Var("X3")
x4 = Var("X4")

h0 = Negate(Imply(x1, And(x1, x2)))  # !(x1 -> (x1 & x2))
h1 = Equiv(x1, Imply(x2, x3))  # x1 <-> (x2 -> x3)
h2 = Or(And(x1, x2), And(x3, x4))  # (x1 & x2) || (x3 & x4)
h3 = Negate(Imply(Negate(And(x1, x2)), Negate(x3)))  # !((!(x1 & x2)) -> x3)

h0_nnf = And(x1, Or(Negate(x1), Negate(x2)))
h1_nnf = And(Or(Negate(x1), Or(Negate(x2), x3)), Or(And(x2, Negate(x3)), x1))
h2_nnf = h2
h3_nnf = And(Or(Negate(x1), Negate(x2)), x3)

h0_cnf = h0_nnf
h1_cnf = And(Or(Negate(x1), Or(Negate(x2), x3)), And(Or(x2, x1),
                                                     Or(Negate(x3), x1)))
h2_cnf = And(Or(x1, x3), And(Or(x1, x4), And(Or(x2, x3), Or(x2, x4))))
h3_cnf = h3_nnf


def test_to_nnf_correctness():
    assert to_nnf(h0) == h0_nnf
    assert to_nnf(h1) == h1_nnf
    assert to_nnf(h2) == h2_nnf
    assert to_nnf(h3) == h3_nnf


def test_to_cnf_correctness():
    assert to_cnf(h0) == h0_cnf
    assert to_cnf(h1) == h1_cnf
    assert to_cnf(h2) == h2_cnf
    assert to_cnf(h3) == h3_cnf


p = Var("p")
q = Var("q")
r = Var("r")

g0 = Var("#G0")
g1 = Var("#G1")
g2 = Var("#G2")
g3 = Var("#G3")


f1 = Or(And(p, q), Negate(Or(q, r)))  # (p & q) || !(q || r)

f1_expected_equivs_ands = [g0, Equiv(g0, Or(g1, g2)), Equiv(g1, And(p, q)),
                           Equiv(g2, Negate(g3)), Equiv(g3, Or(q, r))]


f2 = Negate(Imply(Negate(And(p, q)), Negate(r)))  # !(!(p & q) -> !r)
f2_expected_equivs_ands = [g0, Equiv(g0, Negate(g1)),
                           Equiv(g1, Imply(g2, Negate(r))),
                           Equiv(g2, Negate(g3)), Equiv(g3, And(p, q))]


def test_tseitin_equivs_f1():
    assert _get_tseitin_equivs(f1) == f1_expected_equivs_ands


def test_tseitin_equivs_f2():
    assert _get_tseitin_equivs(f2) == f2_expected_equivs_ands
