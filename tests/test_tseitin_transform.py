from bool_transforms.tseitin_transform import tseitin_transform
from parsing.logical_blocks import Var, Or, And, Negate, Equiv, Imply, Func,\
    NEqual
import pytest
from parsing.parse import Parser
from bool_transforms.to_cnf import to_cnf

parser = Parser()

p = Var("p")
q = Var("q")
r = Var("r")

g0 = Var("#G0")
g1 = Var("#G1")
g2 = Var("#G2")
g3 = Var("#G3")

n0 = Var("#N0")
n1 = Var("#N1")

neg_g0 = Negate(g0)
neg_p = Negate(p)

neq_r_n0 = NEqual(r, n0)
neq_q_n0 = NEqual(q, n0)
neq_q_n1 = NEqual(q, n1)
neq_r_n1 = NEqual(r, n1)

f_q_n0 = Func("f", [q, n0])
f_f_q_n0_n0 = Func("f", [Func("f", [q, n0]), n0])
f_n0_n1 = Func("f", [n0, n1])
f_f_q_n0_n1 = Func("f", [Func("f", [q, n0]), n1])


tseitin_formulas_texts = ["(p & q)  |  !(q | r)",
                          "!((!(p & q)) -> !r)"
                          ]

tseitin_expected_equivs = [
    [g0, Equiv(g0, Or(g1, g2)), Equiv(g1, And(p, q)),
     Equiv(g2, Negate(g3)), Equiv(g3, Or(q, r))],

    [g0, Equiv(g0, Negate(g1)), Equiv(g1, Imply(g2, Negate(r))),
     Equiv(g2, Negate(g3)), Equiv(g3, And(p, q))]
]


@pytest.mark.parametrize("formula_text, expected_equivs_ands",
                         zip(tseitin_formulas_texts, tseitin_expected_equivs),
                         ids=tseitin_formulas_texts)
def test_tseitin_equivs(formula_text, expected_equivs_ands):
    formula = parser.parse(formula_text)
    expected_result = [to_cnf(equiv) for equiv in expected_equivs_ands]
    assert tseitin_transform(formula) == expected_result
