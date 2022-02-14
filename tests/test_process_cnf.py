from typing import Dict
from process_cnf import cnf_conjunction_to_ints
from logical_blocks import Var, Or, And, Negate, Imply, Equal, NEqual, Atom
from bool_transforms import tseitin_transform

p = Var("p")
q = Var("q")
r = Var("r")

g0 = Var("#G0")
g1 = Var("#G1")
g2 = Var("#G2")
g3 = Var("#G3")


def add_negations_to_mapping(mapping: Dict[Atom, int]):
    old_keys = list(mapping.keys())
    for lit in old_keys:
        if isinstance(lit, Equal):
            mapping[NEqual(lit.left, lit.right)] = -mapping[lit]
        else:
            mapping[Negate(lit)] = -mapping[lit]
    return mapping


def is_equivalent_mapping(int_format1, mapping1, int_format2, mapping2):
    inverse_mapping1 = {v: k for (k, v) in mapping1.items()}
    inversed_int_format1 = []
    for clause in int_format1:
        inversed_int_format1.append({inverse_mapping1[int_lit] for
                                     int_lit in clause})

    format1_in_mapping2 = []
    for clause in inversed_int_format1:
        format1_in_mapping2.append({mapping2[lit] for lit in clause})

    return format1_in_mapping2 == int_format2


def test_mapping_f1():  # (p & q) || !(q || r)
    f1 = Or(And(p, q), Negate(Or(q, r)))
    f1_tseitin_form = tseitin_transform(f1)

    expected_f1_mapping = {g0: 1, g1: 2, g2: 3, p: 4, q: 5, g3: 6, r: 7}
    expected_f1_mapping = add_negations_to_mapping(expected_f1_mapping)

    expected_f1_int_format = [{1}, {-1, 2, 3}, {-2, 1}, {-3, 1}, {-2, 4},
                              {-2, 5}, {-4, -5, 2}, {-3, -6}, {3, 6},
                              {-6, 5, 7}, {-5, 6}, {-7, 6}]

    f1_ints_rep, f1_mapping = cnf_conjunction_to_ints(f1_tseitin_form)
    assert is_equivalent_mapping(f1_ints_rep, f1_mapping,
                                 expected_f1_int_format, expected_f1_mapping)


def test_mapping_f2():  # !(!(p & q) -> !r)
    f2 = Negate(Imply(Negate(And(p, q)), Negate(r)))
    f2_tseitin_form = tseitin_transform(f2)

    expected_f2_mapping = {g0: 1, g1: 2, g2: 3, r: 4, g3: 5, p: 6, q: 7}
    expected_f2_mapping = add_negations_to_mapping(expected_f2_mapping)

    expected_f2_int_format = [{1}, {-1, -2}, {2, 1}, {-2, -3, -4}, {3, 2},
                              {4, 2}, {-3, -5}, {5, 3}, {-5, 6},
                              {-5, 7}, {-7, -6,  5}]
    f2_ints_rep, f2_mapping = cnf_conjunction_to_ints(f2_tseitin_form)
    assert is_equivalent_mapping(f2_ints_rep, f2_mapping,
                                 expected_f2_int_format, expected_f2_mapping)
