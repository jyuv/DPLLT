import pytest

from constants import ResultCode
from parsing.logical_blocks import Or, And, Imply, Negate
from parsing.parse import Parser

from solvers.DPLLT import DPLLT
from tests.test_utils import verify_unabstracted_assignment
from theories.TQTheory import TQTheory

solver_with_negatives = DPLLT(TQTheory(support_negative_vars=True))
solver_without_negatives = DPLLT(TQTheory(support_negative_vars=False))
parser = Parser()

simple_cases_strs = [
    "[1] < 0",
    "([1, -1, 0] = 3) & ([2, 1, 0] < 1)",
    "([1, 1] >= 1) & ([1, 1] < -1)",
    "([-1, -1] >= -3) & ([-2, 1] >= 5)",
    "([-2, -3, -1] >= -5) & (([-4, -1, -2] >= -11) & ([-3, -4, -2] >= -8))",
    "([-3, -2, -1, -4] >= -225) & (([-1, -1, -1, -1] >= -117) & "
    "([-4, -3, -3, -4] >= -420))"
]

expected_results_codes_with_negatives = [
    ResultCode.SAT,
    ResultCode.SAT,
    ResultCode.UNSAT,
    ResultCode.SAT,
    ResultCode.SAT,
    ResultCode.SAT,
]

expected_results_codes_without_negatives = [
    ResultCode.UNSAT,
    ResultCode.UNSAT,
    ResultCode.UNSAT,
    ResultCode.UNSAT,
    ResultCode.SAT,
    ResultCode.SAT,
]

RESULT_CODE_LOC = 0
ASSIGNMENT_LOC = 1


@pytest.mark.parametrize("formula_str, expected_result_code",
                         zip(simple_cases_strs,
                             expected_results_codes_with_negatives),
                         ids=simple_cases_strs)
def test_simple_cases_with_negatives(formula_str, expected_result_code):
    formula = parser.parse(formula_str)
    result_with_negatives = solver_with_negatives.solve(formula)

    result_code = result_with_negatives[RESULT_CODE_LOC]
    assignment = result_with_negatives[ASSIGNMENT_LOC]

    assert result_code == expected_result_code
    if expected_result_code == ResultCode.SAT:
        assert verify_unabstracted_assignment(formula, assignment)


@pytest.mark.parametrize("formula_str, expected_result_code",
                         zip(simple_cases_strs,
                             expected_results_codes_without_negatives),
                         ids=simple_cases_strs)
def test_simple_cases_without_negatives(formula_str, expected_result_code):
    formula = parser.parse(formula_str)
    result_without_negatives = solver_without_negatives.solve(formula)

    result_code = result_without_negatives[RESULT_CODE_LOC]
    assignment = result_without_negatives[ASSIGNMENT_LOC]

    assert result_code == expected_result_code

    if expected_result_code == ResultCode.SAT:
        assert verify_unabstracted_assignment(formula, assignment)


def test_big_case():
    l1 = parser.parse("[1, 2, 3, 4, 5, 6, 7, 8] < 123")
    l2 = parser.parse("[8, 0, 6, 0, 4, 0, 2, 0] = 321")
    l3 = parser.parse("[0, 0, 1, 0, 0, 1, 0, 0] != 222")
    l4 = parser.parse("[1, -1, 1, -1, 1, -1, 1, -1] >= 111")
    l5 = parser.parse("[0, 0, 1, 1, 0, 0, 2, 3] >= 222")
    l6 = parser.parse("[3, 2, 1, 3, 0, 5, 0, -1] < 333")
    l7 = parser.parse("[-1, -2, 3, 4, -5, 0, 1, 0] >= 135")
    l8 = parser.parse("[0, 0, 1, 0, 3, -1, 0, 0] < 246")

    formula = Imply(
        And(
            And(
                Or(And(l1, l2), l3),
                Negate(l4)),
            Or(
                And(Negate(l2), Or(l1, l5)),
                l6)),
        Or(
            Or(l7, l8),
            And(l1, l4)))

    res_with_negatives = solver_with_negatives.solve(formula)
    res_without_negatives = solver_without_negatives.solve(formula)

    assert res_with_negatives[RESULT_CODE_LOC] == ResultCode.SAT
    assert res_without_negatives[RESULT_CODE_LOC] == ResultCode.SAT

    with_negatives_assignment = res_with_negatives[ASSIGNMENT_LOC]
    without_negatives_assignment = res_without_negatives[ASSIGNMENT_LOC]

    assert verify_unabstracted_assignment(formula,
                                          with_negatives_assignment)
    assert verify_unabstracted_assignment(formula,
                                          without_negatives_assignment)
