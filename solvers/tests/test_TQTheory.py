import pytest
import numpy as np
from constants import ResultCode
from parsing.logical_blocks import Geq, Less

from parsing.parse import Parser
from solvers.theories.TQTheory import TQTheory

parser = Parser()
theory_with_negatives = TQTheory(support_negative_vars=True)
theory_without_negatives = TQTheory(support_negative_vars=False)

regular_case_map = {1: Geq(np.array([1, 0]), 6),
                    2: Geq(np.array([0, 1]), 6),
                    3: Geq(np.array([1, 1]), 11),
                    -1: Less(np.array([1, 0]), 6),
                    -2: Less(np.array([0, 1]), 6),
                    -3: Less(np.array([1, 1]), 11)}

# case in which the result can depend on whether negative vars are supported
special_case_map = {1: Geq(np.array([-1, -1]), -3),
                    2: Geq(np.array([-2, 1]), 5),
                    -1: Less(np.array([-1, -1]), -3),
                    -2: Less(np.array([-2, 1]), 5)}

regular_all_seqs = {tuple(), (1, ), (2, ), (3, ), (-1, ), (-2, ), (-3, ),
                    (1, 2), (1, 3), (2, 3), (1, -2), (1, -3), (2, -3),
                    (-1, 2), (-1, 3), (-2, 3), (-1, -2), (-1, -3), (-2, -3),
                    (1, 2, -3), (1, -2, 3), (-1, 2, 3),
                    (1, -2, -3), (-1, 2, -3), (1, 2, 3), (-1, -2, -3)}

regular_invalid_seqs = {(1, 2, -3)}
regular_valid_seqs = regular_all_seqs.difference(regular_invalid_seqs)


@pytest.mark.parametrize("assignments_seq", regular_valid_seqs, ids=repr)
def test_sat_assignments_with_negatives(assignments_seq):
    theory_with_negatives.reset()
    theory_with_negatives.register_abstraction_map(regular_case_map)

    for assignment_int in assignments_seq:
        theory_with_negatives.process_assignment(assignment_int)
        res = theory_with_negatives.analyze_satisfiability()
        assert res == (ResultCode.SAT, None)


@pytest.mark.parametrize("assignments_seq", regular_valid_seqs, ids=repr)
def test_sat_assignments_without_negatives(assignments_seq):
    theory_without_negatives.reset()
    theory_without_negatives.register_abstraction_map(regular_case_map)

    for assignment_int in assignments_seq:
        theory_without_negatives.process_assignment(assignment_int)
        res = theory_without_negatives.analyze_satisfiability()
        assert res == (ResultCode.SAT, None)


@pytest.mark.parametrize("assignments_seq", regular_all_seqs, ids=repr)
def test_no_t_propagations_without_negatives(assignments_seq):
    theory_without_negatives.reset()
    theory_without_negatives.register_abstraction_map(regular_case_map)

    for assignment_int in assignments_seq:
        theory_without_negatives.process_assignment(assignment_int)
        assert theory_without_negatives.pop_t_propagation() is None


@pytest.mark.parametrize("assignments_seq", regular_all_seqs, ids=repr)
def test_no_t_propagations_with_negatives(assignments_seq):
    theory_with_negatives.reset()
    theory_with_negatives.register_abstraction_map(regular_case_map)

    for assignment_int in assignments_seq:
        theory_with_negatives.process_assignment(assignment_int)
        assert theory_with_negatives.pop_t_propagation() is None


@pytest.mark.parametrize("formula_text", [
    "m < 3",
    "m >= 3",
    "50 < 60",
    "80 >= 10",
    "(a & b) < 50",
    "[1, 2] < a80",
    "[1, 2] >= -80a"
    "[1, -1] >= a"
    "[1, -1] < f(a)",
    "a = 5",
    "5 = a",
    "5 = 5",
    "a != 5",
    "5 != a",
    "5 != 5",
    "[1, 2] = a",
    "[1, 1] != a"
], ids=repr)
def test_preprocess_invalid_args(formula_text):
    with pytest.raises(ValueError):
        formula = parser.parse(formula_text)
        theory_with_negatives.preprocess(formula)


@pytest.mark.parametrize("formula_text, expected_preprocessed_text", [
    ("[-1, 0, 1] < -5", "[-1, 0, 1] < -5"),
    ("[-1, 0, 1] >= -5", "[-1, 0, 1] >= -5"),
    ("[-1, 0, 1] = -5", "([-1, 0, 1] >= -5) & ([1, 0, -1] >= 5)"),
    ("[-1, 0, 1] != -5", "!(([-1, 0, 1] >= -5) & ([1, 0, -1] >= 5))")
], ids=["Less case", "Geq case", "Equality case", "Inequality case"])
def test_preprocess_valid_args(formula_text, expected_preprocessed_text):
    formula = parser.parse(formula_text)
    expected_preprocessed = parser.parse(expected_preprocessed_text)

    assert theory_with_negatives.preprocess(formula) == expected_preprocessed


def test_conflict_recovery_to_empty():
    theory_with_negatives.reset()
    theory_without_negatives.reset()

    theory_with_negatives.register_abstraction_map(regular_case_map)
    theory_without_negatives.register_abstraction_map(regular_case_map)

    theory_with_negatives.process_assignment(1)
    theory_without_negatives.process_assignment(1)
    theory_with_negatives.process_assignment(2)
    theory_without_negatives.process_assignment(2)
    theory_with_negatives.process_assignment(3)
    theory_without_negatives.process_assignment(3)

    theory_with_negatives.conflict_recovery([])
    theory_without_negatives.conflict_recovery([])

    assert theory_with_negatives.assignment == set()
    assert theory_without_negatives.assignment == set()

    assert theory_with_negatives.A is None
    assert theory_without_negatives.A is None

    assert theory_with_negatives.b is None
    assert theory_without_negatives.b is None


def test_conflict_recovery_to_sat():
    theory_with_negatives.reset()
    theory_without_negatives.reset()

    theory_with_negatives.register_abstraction_map(regular_case_map)
    theory_without_negatives.register_abstraction_map(regular_case_map)

    theory_with_negatives.process_assignment(1)
    theory_without_negatives.process_assignment(1)
    theory_with_negatives.process_assignment(-2)
    theory_without_negatives.process_assignment(-2)
    theory_with_negatives.process_assignment(3)
    theory_without_negatives.process_assignment(3)

    theory_with_negatives.conflict_recovery([1, -2])
    theory_without_negatives.conflict_recovery([1, -2])

    assert theory_with_negatives.assignment == {1, -2}
    assert theory_without_negatives.assignment == {1, -2}

    assert np.array_equal(theory_with_negatives.A,
                          np.array([[-1, 1, 0, 0, 0],
                                    [0, 0, 1, -1, 1]])
                          )
    assert np.array_equal(theory_without_negatives.A,
                          np.array([[-1, 0, 0],
                                    [0, 1, 1]])
                          )

    expected_b = np.array([-6, 6]).reshape((2, 1))
    assert np.array_equal(theory_with_negatives.b, expected_b)
    assert np.array_equal(theory_without_negatives.b, expected_b)


@pytest.mark.parametrize("assignments_seq", regular_invalid_seqs, ids=repr)
def test_unsat_assignments_independent_negatives(assignments_seq):
    theory_with_negatives.reset()
    theory_without_negatives.reset()

    theory_with_negatives.register_abstraction_map(regular_case_map)
    theory_without_negatives.register_abstraction_map(regular_case_map)

    for assignment_int in assignments_seq:
        theory_with_negatives.process_assignment(assignment_int)
        theory_without_negatives.process_assignment(assignment_int)

    expected_conflict_clause = {-i for i in assignments_seq}
    expected_result = (ResultCode.UNSAT, expected_conflict_clause)

    assert theory_with_negatives.analyze_satisfiability() == expected_result
    assert theory_without_negatives.analyze_satisfiability() == expected_result


@pytest.mark.parametrize("assignments_seq", [(1, 2)], ids=repr)
def test_unsat_assignments_negatives_dependent(assignments_seq):
    theory_with_negatives.reset()
    theory_without_negatives.reset()

    theory_with_negatives.register_abstraction_map(special_case_map)
    theory_without_negatives.register_abstraction_map(special_case_map)

    for assignment_int in assignments_seq:
        theory_with_negatives.process_assignment(assignment_int)
        theory_without_negatives.process_assignment(assignment_int)

    unsat_conflict_clause = {-i for i in assignments_seq}
    unsat_result = (ResultCode.UNSAT, unsat_conflict_clause)
    sat_result = (ResultCode.SAT, None)

    assert theory_with_negatives.analyze_satisfiability() == sat_result
    assert theory_without_negatives.analyze_satisfiability() == unsat_result


@pytest.mark.parametrize("formula_str", [
    "[1, 2] < [1, 2]",
    "3 >= 2",
    "3 = 4",
    "[1, 2] = [1, 2]",
    "5 != 3",
    "[1, 2] != [2, 1]",
    "([1, 2, 3] < 5) -> (([1, 1] = 5) & ([1, -1] != [1]))"
], ids=repr)
def test_invalid_args(formula_str):
    formula = parser.parse(formula_str)
    with pytest.raises(ValueError):
        theory_with_negatives.preprocess(formula)


equalities_raw_strs = [
    "[3, 1] = 5",
    "[3, 1] != 5",
    "([1, 1] < 2) & (([1, 2] >= 5) | ([3, 1] = 5))"
]

equalities_preprocessed_strs = [
    "([3, 1] >= 5) & ([-3, -1] >= -5)",
    "!(([3, 1] >= 5) & ([-3, -1] >= -5))",
    "([1, 1] < 2) & (([1, 2] >= 5) | (([3, 1] >= 5) & ([-3, -1] >= -5)))"
]


@pytest.mark.parametrize("formula_str, expected_formula_str",
                         zip(equalities_raw_strs, equalities_preprocessed_strs),
                         ids=equalities_raw_strs)
def test_preprocess_equalities(formula_str, expected_formula_str):
    formula = parser.parse(formula_str)
    expected_formula = parser.parse(expected_formula_str)
    assert theory_with_negatives.preprocess(formula) == expected_formula
