import pytest
from parsing.parse import Parser
from bool_transforms.to_cnf import to_nnf, to_cnf

parser = Parser()


formulas_texts = [
    "!(x1 -> (x1 & x2))",
    "x1 <-> (x2 -> x3)",
    "(x1 & x2) | (x3 & x4)",
    "!((!(x1 & x2)) -> (!x3))",
]

formulas_nnf_texts = [
    "x1 & ((!x1) | (!x2))",
    "((!x1) | ((!x2) | x3)) & ((x2 & (!x3)) | x1)",
    "(x1 & x2) | (x3 & x4)",
    "((!x1) | (!x2)) & x3",
]

formulas_cnf_texts = [
    "x1 & ((!x1) | (!x2))",
    "((!x1) | ((!x2) | x3))  &  ((x2 | x1) & ((!x3) | x1))",
    "(x1 | x3)  &  ((x1 | x4) & ((x2 | x3) & (x2 | x4)))",
    "((!x1) | (!x2)) & x3",
]


@pytest.mark.parametrize(
    "formula_text, expected_nnf_text",
    zip(formulas_texts, formulas_nnf_texts),
    ids=formulas_texts,
)
def test_to_nnf_correctness(formula_text, expected_nnf_text):
    formula = parser.parse(formula_text)
    expected_nnf = parser.parse(expected_nnf_text)
    assert to_nnf(formula) == expected_nnf


@pytest.mark.parametrize(
    "formula_text, expected_cnf_text",
    zip(formulas_texts, formulas_cnf_texts),
    ids=formulas_texts,
)
def test_to_cnf_correctness(formula_text, expected_cnf_text):
    formula = parser.parse(formula_text)
    expected_cnf = parser.parse(expected_cnf_text)
    assert to_cnf(formula) == expected_cnf
