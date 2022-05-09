import pytest

from bool_transforms.process_cnf import to_abstract_cnf_conjunction
from parsing.logical_blocks import Var, Negate, Equal, NEqual, Func
from parsing.parse import Parser

p = Var("p")
q = Var("q")
r = Var("r")

g0 = Var("#G0")
g1 = Var("#G1")
g2 = Var("#G2")
g3 = Var("#G3")

neg_g0 = Negate(g0)
neg_g1 = Negate(g1)
neg_g2 = Negate(g2)
neg_g3 = Negate(g3)
neg_p = Negate(p)
neg_q = Negate(q)
neg_r = Negate(r)

n0 = Var("#N0")
n1 = Var("#N1")
f_n0_n1 = Func("f", [n0, n1])
f_q_n0 = Func("f", [q, n0])
f_f_q_n0_n0 = Func("f", [Func("f", [q, n0]), n0])
f_f_q_n0_n1 = Func("f", [Func("f", [q, n0]), n1])
neq_q_n0 = NEqual(q, n0)
neq_r_n0 = NEqual(r, n0)
neq_r_n1 = NEqual(r, n1)
neq_q_n1 = NEqual(q, n1)
eq_q_r = Equal(q, r)
neq_q_r = NEqual(q, r)

parser = Parser()


def to_lit_conjunction(ints_conjunction, int_to_lit):
    return [{int_to_lit[i] for i in cl} for cl in ints_conjunction]


formulas_text = ["(p & q) | !(q | r)", "!((!(p & q)) -> !r)"]

expected_lit_formats = [
    [
        {g0},
        {neg_g0, g1, g2},
        {neg_g1, g0},
        {neg_g2, g0},
        {neg_g1, p},
        {neg_g1, q},
        {neg_p, neg_q, g1},
        {neg_g2, neg_g3},
        {g2, g3},
        {neg_g3, q, r},
        {neg_q, g3},
        {neg_r, g3},
    ],
    [
        {g0},
        {neg_g0, neg_g1},
        {g1, g0},
        {neg_g1, neg_g2, neg_r},
        {g2, g1},
        {r, g1},
        {neg_g2, neg_g3},
        {g3, g2},
        {neg_g3, p},
        {neg_g3, q},
        {neg_q, neg_p, g3},
    ],
]


@pytest.mark.parametrize(
    "formula_text, expected_lit_clauses",
    zip(formulas_text, expected_lit_formats),
    ids=formulas_text,
)
def test_mapping_regular(formula_text, expected_lit_clauses):
    formula = parser.parse(formula_text)
    int_cnf_formula, abstraction_map, _ = to_abstract_cnf_conjunction(formula)
    lit_clauses = to_lit_conjunction(int_cnf_formula, abstraction_map)

    assert lit_clauses == expected_lit_clauses


clauses_equal_case = [{g0}, {neg_g0, p}, {neg_g0, eq_q_r}, {neg_p, g0, neq_q_r}]
clauses_nequal_case = [{g0}, {neg_g0, p}, {neg_g0, neq_q_r}, {neg_p, g0, eq_q_r}]

negations_eqs_formulas_texts = [
    "p & ((!q) = r)",
    "p & (q = !r)",
    "p & ((!q) = !r)",
    "p & ((!q) != r)",
    "p & (q != !r)",
    "p & ((!q) != !r)",
]

negations_expected_lit_clauses = [
    clauses_nequal_case,
    clauses_nequal_case,
    clauses_equal_case,
    clauses_equal_case,
    clauses_equal_case,
    clauses_nequal_case,
]


@pytest.mark.parametrize(
    "formula_text, expected_lit_clauses",
    zip(negations_eqs_formulas_texts, negations_expected_lit_clauses),
    ids=negations_eqs_formulas_texts,
)
def test_mapping_negations_eqs(formula_text, expected_lit_clauses):
    formula = parser.parse(formula_text)
    int_cnf_formula, abstraction_map, _ = to_abstract_cnf_conjunction(formula)
    lit_clauses = to_lit_conjunction(int_cnf_formula, abstraction_map)
    assert lit_clauses == expected_lit_clauses


func_args_negations_texts = [
    "p & f(q, !r)",
    "p & f(!q, !r)",
    "p & f(f(q, !r), !r)",
    "p & f(f(q, !r), !q)",
]

func_args_negations_expected_lit_clauses = [
    [{g0}, {neg_g0, p}, {neg_g0, f_q_n0}, {neg_p, Negate(f_q_n0), g0}, {neq_r_n0}],
    [
        {g0},
        {neg_g0, p},
        {neg_g0, f_n0_n1},
        {neg_p, Negate(f_n0_n1), g0},
        {neq_q_n0},
        {neq_r_n1},
    ],
    [
        {g0},
        {neg_g0, p},
        {neg_g0, f_f_q_n0_n0},
        {neg_p, Negate(f_f_q_n0_n0), g0},
        {neq_r_n0},
    ],
    [
        {g0},
        {neg_g0, p},
        {neg_g0, f_f_q_n0_n1},
        {neg_p, Negate(f_f_q_n0_n1), g0},
        {neq_r_n0},
        {neq_q_n1},
    ],
]


@pytest.mark.parametrize(
    "formula_text, expected_lit_clauses",
    zip(func_args_negations_texts, func_args_negations_expected_lit_clauses),
    ids=func_args_negations_texts,
)
def test_mapping_func_args_negations(formula_text, expected_lit_clauses):
    formula = parser.parse(formula_text)
    int_cnf_formula, abstraction_map, _ = to_abstract_cnf_conjunction(formula)
    lit_clauses = to_lit_conjunction(int_cnf_formula, abstraction_map)
    assert lit_clauses == expected_lit_clauses
