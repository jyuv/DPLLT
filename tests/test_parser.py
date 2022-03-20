import pytest

from parsing.logical_blocks import *
from parsing.parse import Parser


a = Var("a")
neg_a = Negate(a)
b = Var("b")
neg_b = Negate(b)
c = Var("c")
r = Var("r")
neg_r = Negate(r)
v = Var("v")
neg_v = Negate(v)
e = Var("e")
neg_e = Negate(e)
m = Var("m")
n = Var("n")
neg_n = Negate(n)
x = Var("x")
neg_x = Negate(x)
y = Var("y")
zz = Var("zz")

parser = Parser()


@pytest.mark.parametrize("atom_str, expected_parsed", [
    ("x", x),
    ("zz", zz),
    ("x & y", And(x, y)),
    ("x | y", Or(x, y)),
    ("x -> y", Imply(x, y)),
    ("y <- x", Imply(x, y)),
    ("x <-> y", Equiv(x, y)),
    ("5 < 7", Less(5, 7)),
    ("[1, 1] >= 7", Geq(np.array([1, 1]), 7)),
    ("a = b", Equal(a, b)),
    ("a != b", NEqual(a, b)),
    ("!x", neg_x),
    ("f(a)", Func("f", [a]))
], ids=repr)
def test_atoms(atom_str, expected_parsed):
    assert parser.parse(atom_str) == expected_parsed


complex_formulas_strs = ["((!x)&y)|f(x,y)",
                         "a & (!a)",
                         "a | !b",
                         "!!b",
                         "(a & b) | ((!a) & (c -> b))",
                         "(((a|(!b))|(r&(!a)))&((c&r)|(c->((!r)&b))))&"
                         "(((n->a)&((!r)|n))->((r&n)&(a|(!n))))"]

expected_complex_formulas = [Or(And(Negate(x), y), Func("f", (x, y))),
                             And(a, neg_a),
                             Or(a, neg_b),
                             Negate(neg_b),
                             Or(And(a, b), And(neg_a, Imply(c, b))),
                             And(
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
                             ]


@pytest.mark.parametrize("formula_str, expected_parsed",
                         zip(complex_formulas_strs, expected_complex_formulas),
                         ids=complex_formulas_strs)
def test_complex_formulas(formula_str, expected_parsed):
    assert parser.parse(formula_str) == expected_parsed


def test_empty():
    assert parser.parse("") is None


arrays_formulas_strs = ["[5,3,-2,1] < 4",
                        "[5,3,-2,1] >= 4",
                        "([1, 3] < 5) & (a | b)"]

arrays_formulas = [Less(np.array([5, 3, -2, 1]), 4),
                   Geq(np.array([5, 3, -2, 1]), 4),
                   And(Less(np.array([1, 3]), 5), Or(a, b))]


@pytest.mark.parametrize("formula_str, expected_formula",
                         zip(arrays_formulas_strs, arrays_formulas),
                         ids=arrays_formulas_strs)
def test_array_parsing(formula_str, expected_formula):
    assert parser.parse(formula_str) == expected_formula


@pytest.mark.parametrize("invalid_array_str", [
    "[,] < 4",
    "[1,] < 4",
    "[1,,2] >= 4",
    "[1,-12a3] < 4",
    "[] < 5"], ids=repr)
def test_invalid_arrays(invalid_array_str):
    with pytest.raises(ValueError):
        parser.parse(invalid_array_str)


@pytest.mark.parametrize("ambiguous_formula_str", [
    "a & b & c",
    "(!a & b)",
    "(a & b) -> (!(c) | f)",
    "(a & ()) | d"
])
def test_ambiguous_formulas(ambiguous_formula_str):
    with pytest.raises(ValueError):
        parser.parse(ambiguous_formula_str)


@pytest.mark.parametrize("unbalanced_parentheses_str", [
    "((a)",
    "a & (b -> (!c)))",
    "((a))) & (c)",
    ")(a)"
])
def test_unbalanced_parentheses(unbalanced_parentheses_str):
    with pytest.raises(ValueError):
        parser.parse(unbalanced_parentheses_str)


@pytest.mark.parametrize("invalid_delimiter_str", [
    "b,c",
    "f(a, v) & c,",
    "(,)"
])
def test_delimiter_invalidity(invalid_delimiter_str):
    with pytest.raises(ValueError):
        parser.parse(invalid_delimiter_str)


def test_function_in_function():
    text = "p & f(f(q, !r), !r)"
    p = Var("p")
    q = Var("q")
    expected_result = And(p, Func("f", [Func("f", [q, neg_r]), neg_r]))
    assert parser.parse(text) == expected_result

