import pytest
from parse import Parser

parser = Parser()


is_literal_params = [
    ("x1", True),
    ("!x1", True),
    ("!!x1", False),
    ("(!x1) -> x2", False),
    ("x2 <-> x3", False),
    ("x2 & x3", False),
    ("x1 | x2", False),
    ("(x1 & x2) | x3", False)
]


@pytest.mark.parametrize("formula_text, bool_is_literal",
                         is_literal_params,
                         ids=[repr(is_lit[0]) for is_lit in is_literal_params])
def test_is_literal(formula_text, bool_is_literal):
    formula = parser.parse(formula_text)
    assert formula.is_literal() == bool_is_literal


# Todo: add here =, !=,  >=, <, functions, double negations,
#  double negations as args.
@pytest.mark.parametrize("formula_text", [
    "!(X1->(X1&X2))",
    "!(X1<->(X1&X2))",
    "(X1|!X2)&(X3->X2)"
    "a = b",
    "a = (c = d)",
    "a != b",
    "a != (c & d)",
    "[1, 2] < 3",
    "!([1, 2] < 3)",
    "[1, 2] >= 3",
    "!([1, 2] >= 3)",
    "f(a, b)",
    "f(a, b & c)",
    "f(a = b, c | (d & s))"
    "!!x",
    "!!(a = b)",
    "!!!x",
    "!!!(a = b)"
])
def test_str(formula_text):
    formula = parser.parse(formula_text)
    assert str(formula).replace(" ", "") == formula_text.replace(" ", "")


# Todo: add __eq__ & __hash__ tests
#  Make sure equalities with isinstance(type(self)) works

# Todo: add here =, !=, >=, <, functions
negations_params = [
    ("!x1", "x1"),
    ("!!x2", "!x2"),
    ("x1 & x2", "(!x1) | !x2"),
    ("(!x1) & x2", "(!!x1) | !x2"),
    ("x1 | x2", "(!x1) & !x2"),
    ("(!!x1) | !x2", "(!!!x1) & !!x2")
]


@pytest.mark.parametrize("formula_text, expected_negation_text",
                         negations_params,
                         ids=[neg_param[0] for neg_param in negations_params])
def test_negations(formula_text, expected_negation_text):
    formula = parser.parse(formula_text)
    expected_negation = parser.parse(expected_negation_text)
    assert formula.negate() == expected_negation


to_basic_params = [
    ("x1 -> x2", "(!x1) | x2"),
    ("(!x1) -> !x2", "(!!x1) | !x2"),
    ("(x1 & x2) -> x3", "(!(x1 & x2)) | x3"),
    ("x1 <-> x2", "((!x1) | x2) & ((!x2) | x1)"),
    ("(!x1) <-> !x2", "((!!x1) | !x2) & ((!!x2) | !x1)"),
    ("(x1 & x2) <-> x3", "((!(x1 & x2)) | x3) & ((!x3) | (x1 & x2))")
]


@pytest.mark.parametrize("formula_text, basic_form_text",
                         to_basic_params,
                         ids=[tb_param[0] for tb_param in to_basic_params])
def test_to_basic(formula_text, basic_form_text):
    formula = parser.parse(formula_text)
    basic_form = parser.parse(basic_form_text)
    assert formula.to_basic() == basic_form


@pytest.mark.parametrize("formula_text, cnf_distribute_text", [
    ("x1 | x2", "x1 | x2"),
    ("(!x1) | (!x2)", "(!x1) | (!x2)"),
    ("(!!x1) | (!x2)", "(!!x1) | (!x2)"),
    ("(x1 & x2) | x3", "(x1 | x3) &  (x2 | x3)"),
    ("(x1 & x2) | (!x3)", "(x1 | !x3) & (x2 | !x3)"),
    ("x1 | (x2 & x3)", "(x1 | x2) & (x1 | x3)"),
    ("(!x1) | (x2 & x3)", "((!x1) | x2) & ((!x1) | x3)"),
    ("(!(x1 & x2)) | (!x3)", "(!(x1 & x2)) | (!x3)"),
    ("(!x3) | (!(x1 & x2))", "(!x3) | (!(x1 & x2))"),
    ("(x1 & x2) | (x3 & x4)",
     "(x1 | x3) & ((x1 | x4) & ((x2 | x3) & (x2 | x4)))")
])
def test_cnf_distribute(formula_text, cnf_distribute_text):
    formula = parser.parse(formula_text)
    cnf_distribute_form = parser.parse(cnf_distribute_text)
    assert formula.cnf_distribute() == cnf_distribute_form
