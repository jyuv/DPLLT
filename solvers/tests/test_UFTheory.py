import pytest

from constants import ResultCode
from parsing.logical_blocks import Negate, Func, Equal, NEqual
from solvers.theories.UFTheory import UFTheory
from parsing.parse import Parser

parser = Parser()

a, b, c, d, s, t, r, x, y = [parser.parse(t) for t in "abcdstrxy"]

g_x, g_a = [parser.parse(f"g({t})") for t in "xa"]

f_x, f_y, f_s, f_t, f_c, f_a = [parser.parse("f(" + t + ")") for t in
                                "xystca"]

f_3a = parser.parse("f(f(f(a)))")
f_5a = parser.parse("f(f(f(f(f(a)))))")


g_f_x = Func("g", f_x)
f_g_x = Func("f", g_x)
f_g_f_y = Func("f", Func("g", f_y))
f_g_a = Func("f", g_a)
f_ab = Func("f", [a, b])
f_bc = Func("f", [b, c])
g_bc = Func("g", [b, c])
f_fab_b = Func("f", [f_ab, b])
g_fab_fbc = Func("g", [f_ab, f_bc])

uf_theory = UFTheory()


def test_case1():  # (f^3(a) = a) & (f^5(a) = a) & (f(a) != a)
    abs_literals_to_ints = {Equal(f_3a, a): 1,
                            NEqual(f_3a, a): -1,
                            Equal(f_5a, a): 2,
                            NEqual(f_5a, a): -2,
                            Equal(f_a, a): 3,
                            NEqual(f_a, a): -3
                            }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                       abs_literals_to_ints.items()})

    uf_theory.process_assignment(1)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert uf_theory.pop_t_propagation() == 3

    uf_theory.process_assignment(-3)
    assert not uf_theory.check_t_propagations()
    assert uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability() == (ResultCode.UNSAT, {-1, -2, 3})
    assert not uf_theory.pop_t_propagation()

    uf_theory.conflict_recovery([])
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(-3)
    assert not uf_theory.check_t_propagations()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.is_t_conflict()
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(2)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(-1)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()


def test_case2():
    abs_literals_to_ints_2 = {Equal(f_g_x, g_f_x): 1,
                              NEqual(f_g_x, g_f_x): -1,
                              Equal(f_g_f_y, x): 2,
                              NEqual(f_g_f_y, x): -2,
                              Equal(f_y, x): 3,
                              NEqual(f_y, x): -3,
                              Equal(g_f_x, x): 4,
                              NEqual(g_f_x, x): -4
                              }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                         abs_literals_to_ints_2.items()})

    uf_theory.process_assignment(1)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(2)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(-4)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(3)
    assert not uf_theory.check_t_propagations()
    assert uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability() == (ResultCode.UNSAT,
                                                   {-1, -2, 4, -3})
    assert not uf_theory.pop_t_propagation()

    uf_theory.conflict_recovery([1, 2])
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(-3)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()

    uf_theory.process_assignment(4)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()


def test_case3():
    abs_literals_to_ints_3 = {Equal(g_a, c): 1,
                              NEqual(g_a, c): -1,
                              Equal(f_g_a, f_c): 2,
                              NEqual(f_g_a, f_c): -2,
                              Equal(g_a, d): 3,
                              NEqual(g_a, d): -3,
                              Equal(c, d): 4,
                              NEqual(c, d): -4
                              }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                         abs_literals_to_ints_3.items()})

    uf_theory.process_assignment(1)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert uf_theory.pop_t_propagation() == 2

    uf_theory.process_assignment(-2)
    assert not uf_theory.check_t_propagations()
    assert uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability() == (ResultCode.UNSAT, {-1, 2})
    assert not uf_theory.pop_t_propagation()

    uf_theory.conflict_recovery([1])
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(3)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(4)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT


# test case functions with arity = 2
def test_case4():
    abs_literals_to_ints_4 = {Equal(a, b): 1,
                              NEqual(a, b): -1,
                              Equal(b, c): 2,
                              NEqual(b, c): -2,
                              c: 3,
                              Negate(c): -3,
                              Equal(f_ab, f_bc): 4,
                              NEqual(f_ab, f_bc): -4,
                              Equal(b, f_ab): 5,
                              NEqual(b, f_ab): -5,
                              Equal(c, f_bc): 6,
                              NEqual(c, f_bc): -6,
                              Equal(c, f_bc): 6,
                              NEqual(c, f_bc): -6,
                              Equal(g_fab_fbc, g_bc): 7,
                              NEqual(g_fab_fbc, g_bc): -7,
                              Equal(c, f_ab): 8,
                              NEqual(c, f_ab): -8,
                              Equal(b, f_bc): 9,
                              NEqual(b, f_bc): -9,
                              Equal(f_fab_b, g_fab_fbc): 10,
                              NEqual(f_fab_b, g_fab_fbc): -10,
                              }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_4.items()})


    # check a=b ^ b=c --> f(a,b) = f(b,c)
    uf_theory.process_assignment(1)
    uf_theory.process_assignment(2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    # check f=(a,b) ^ c=f(b,c) --> g(f(a,b), f(b,c)) = g(b,c)
    uf_theory.conflict_recovery([])
    uf_theory.process_assignment(6)
    assert not uf_theory.check_t_propagations()
    uf_theory.process_assignment(5)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    # check c=f(a,b) ^ b = f(b,c) not implies g(f(a,b),f(b,c)) = g(b, c)
    # (wrong order)
    uf_theory.conflict_recovery([])
    uf_theory.process_assignment(9)
    uf_theory.process_assignment(8)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    # check b=f(b,c) not implies f(f(a,b), b) = g(f(a,b), f(b,c))
    uf_theory.conflict_recovery([9])
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT


def test_case5():
    abs_literals_to_ints_5 = {Equal(a, b): 1,
                              NEqual(a, b): -1,
                              Equal(s, t): 2,
                              NEqual(s, t): -2,
                              Equal(b, c): 3,
                              NEqual(b, c): -3,
                              Equal(t, r): 4,
                              NEqual(t, r): -4,
                              Equal(f_s, f_t): 5,
                              NEqual(f_s, f_t): -5,
                              Equal(f_s, f_a): 6,
                              NEqual(f_s, f_a): -6,
                              Equal(f_a, f_c): 7,
                              NEqual(f_a, f_c): -7
                              }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_5.items()})

    uf_theory.process_assignment(1)
    uf_theory.process_assignment(2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(3)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(4)
    uf_theory.process_assignment(6)
    uf_theory.process_assignment(-7)
    assert uf_theory.check_t_propagations()
    assert uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability() == (ResultCode.UNSAT,
                                                   {-1, -3, 7})

    uf_theory.conflict_recovery([1])
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.pop_t_propagation()


# check t_propagation of neq and combination of non eqs/neqs with eqs/neqs
def test_case6():
    abs_literals_to_ints_6 = {Equal(a, b): 1,
                              NEqual(a, b): -1,
                              Equal(b, c): 2,
                              NEqual(b, c): -2,
                              Equal(a, c): 3,
                              NEqual(a, c): -3,
                              c: 4,
                              Negate(c): -4
                              }

    uf_theory.reset()
    uf_theory.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_6.items()})

    uf_theory.process_assignment(4)
    uf_theory.process_assignment(1)
    uf_theory.process_assignment(-2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.conflict_recovery([])
    uf_theory.process_assignment(-4)
    assert not uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT
    assert not uf_theory.check_t_propagations()

    uf_theory.process_assignment(1)
    uf_theory.process_assignment(-2)
    assert uf_theory.check_t_propagations()
    assert not uf_theory.is_t_conflict()
    assert uf_theory.analyze_satisfiability()[0] == ResultCode.SAT

    uf_theory.process_assignment(3)
    assert not uf_theory.check_t_propagations()
    assert uf_theory.is_t_conflict()


@pytest.mark.parametrize("formula_str", [
    "[1, 2] < 5",
    "[1, -2] >= 3"
], ids=repr)
def test_invalid_atom_types_check(formula_str):
    formula = parser.parse(formula_str)
    with pytest.raises(ValueError):
        uf_theory.preprocess(formula)
