from process_cnf import to_abstract_cnf_conjunction
from logical_blocks import Var, Or, And, Negate, Imply, Equal, NEqual, Func

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


def test_mapping_f1():  # (p & q) || !(q || r)
    f1 = Or(And(p, q), Negate(Or(q, r)))
    f1_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(f1))
    expected_f1_int_format = [{g0}, {neg_g0, g1, g2}, {neg_g1, g0},
                              {neg_g2, g0}, {neg_g1, p},
                              {neg_g1, q}, {neg_p, neg_q, g1},
                              {neg_g2, neg_g3}, {g2, g3},
                              {neg_g3, q, r}, {neg_q, g3}, {neg_r, g3}]

    assert f1_clauses == expected_f1_int_format


def test_mapping_f2():  # !(!(p & q) -> !r)
    f2 = Negate(Imply(Negate(And(p, q)), neg_r))

    expected_f2_clauses = [{g0}, {neg_g0, neg_g1}, {g1, g0},
                           {neg_g1, neg_g2, neg_r}, {g2, g1},
                           {r, g1}, {neg_g2, neg_g3}, {g3, g2}, {neg_g3, p},
                           {neg_g3, q}, {neg_q, neg_p,  g3}]

    f2_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(f2))
    assert expected_f2_clauses == f2_clauses


def test_mapping_negations_eqs():
    case_eq_f = And(p, Equal(q, r))
    expected_eq_clauses = to_lit_conjunction(
        *to_abstract_cnf_conjunction(case_eq_f))

    case_neq_f = And(p, NEqual(q, r))
    expected_neq_clauses = to_lit_conjunction(
        *to_abstract_cnf_conjunction(case_neq_f))

    case1_f = And(p, Equal(neg_q, r))
    case1_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case1_f))
    assert case1_clauses == expected_neq_clauses

    case2_f = And(p, Equal(q, neg_r))
    case2_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case2_f))
    assert case2_clauses == expected_neq_clauses

    case3_f = And(p, Equal(neg_q, neg_r))
    case3_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case3_f))
    assert case3_clauses == expected_eq_clauses

    case4_f = And(p, NEqual(neg_q, r))
    case4_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case4_f))
    assert case4_clauses == expected_eq_clauses

    case5_f = And(p, NEqual(q, neg_r))
    case5_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case5_f))
    assert case5_clauses == expected_eq_clauses

    case6_f = And(p, NEqual(neg_q, neg_r))
    case6_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case6_f))
    assert case6_clauses == expected_neq_clauses


def to_lit_conjunction(ints_conjunction, int_to_lit):
    return [{int_to_lit[i] for i in cl} for cl in ints_conjunction]


def test_mapping_negations_args():
    expected_c1_clauses = [{g0}, {neg_g0, p}, {f_q_n0, neg_g0},
                           {neg_p, Negate(f_q_n0), g0}, {neq_r_n0}]

    expected_c2_clauses = [{g0}, {neg_g0, p}, {f_n0_n1, neg_g0},
                           {neg_p, Negate(f_n0_n1), g0}, {neq_q_n0}, {neq_r_n1}]

    expected_c3_clauses = [{g0}, {neg_g0, p}, {f_f_q_n0_n0, neg_g0},
                           {neg_p, Negate(f_f_q_n0_n0), g0}, {neq_r_n0}]

    expected_c4_clauses = [{g0}, {neg_g0, p}, {f_f_q_n0_n1, neg_g0},
                           {neg_p, Negate(f_f_q_n0_n1), g0},
                           {neq_r_n0}, {neq_q_n1}]

    case1_f = And(p, Func("f", [q, Negate(r)]))
    case2_f = And(p, Func("f", [Negate(q), Negate(r)]))

    case3_f = And(p, Func("f", [Func("f", [q, Negate(r)]), Negate(r)]))
    case4_f = And(p, Func("f", [Func("f", [q, Negate(r)]), Negate(q)]))

    c1_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case1_f))
    c2_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case2_f))
    c3_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case3_f))
    c4_clauses = to_lit_conjunction(*to_abstract_cnf_conjunction(case4_f))

    assert expected_c1_clauses == c1_clauses
    assert expected_c2_clauses == c2_clauses
    assert expected_c3_clauses == c3_clauses
    assert expected_c4_clauses == c4_clauses
