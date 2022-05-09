import pytest
from parsing.parse import Parser
from solvers.theories.PropositionalTheory import PropositionalTheory

theory = PropositionalTheory()
parser = Parser()


@pytest.mark.parametrize("formula_str", [
    "[1, 2] < 3",
    "f(a)",
    "a & (f(a))",
    "a = b",
    "a != b",
    "[1, 2] >= 3"
], ids=repr)
def test_atom_types_checks_errors(formula_str):
    formula = parser.parse(formula_str)

    with pytest.raises(ValueError):
        theory.preprocess(formula)
