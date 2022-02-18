from constants import ResultCode
from logical_blocks import Var, Negate, Func, Equal, NEqual
from theories.UFTheory import UFTheory

def test_case1():  # (f^3(a) = a) & (f^5(a) = a) & (f(a) != a)
    a = Var("a")
    f_a = Func("f", a)
    f_3a = Func("f", Func("f", Func("f", a)))
    f_5a = Func("f", Func("f", Func("f", Func("f", Func("f", a)))))
    cnf_list = [[Equal(f_3a, a)], [Equal(f_5a, a)], [NEqual(f_a, a)]]
    abs_literals_to_ints = {Equal(f_3a, a): 1,
                            NEqual(f_3a, a): -1,
                            Equal(f_5a, a): 2,
                            NEqual(f_5a, a): -2,
                            Equal(f_a, a): 3,
                            NEqual(f_a, a): -3
                            }

    t_solver = UFTheory()
    t_solver.register_abstraction_map({v: k for (k, v) in
                                            abs_literals_to_ints.items()})

    t_solver.process_assignment(1)
    assert not t_solver.check_t_propagations()
    assert not t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 0
    assert t_solver.cur_assignment == [1]
    assert t_solver.assignments_log == [tuple(), (1,)]
    assert t_solver.is_same_rep(f_3a, a)
    assert t_solver.unassigned_ints == {2, 3}

    t_solver.process_assignment(2)
    assert t_solver.check_t_propagations()
    assert not t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert t_solver.pop_t_propagation() == 3
    assert len(t_solver.active_neqs) == 0
    assert t_solver.cur_assignment == [1, 2]
    assert t_solver.assignments_log == [tuple(), (1,), (1, 2)]
    assert t_solver.is_same_rep(f_3a, a)
    assert t_solver.unassigned_ints == {3}

    t_solver.process_assignment(-3)
    assert not t_solver.check_t_propagations()
    assert t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability() == (ResultCode.UNSAT, {-1, -2, 3})
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 1
    assert t_solver.cur_assignment == [1, 2, -3]
    assert t_solver.assignments_log == [tuple(), (1,), (1, 2), (1, 2, -3)]
    assert t_solver.is_same_rep(f_3a, a)
    assert t_solver.is_same_rep(f_5a, f_3a)
    assert t_solver.unassigned_ints == set()

    t_solver.conflict_recovery([])
    assert not t_solver.check_t_propagations()
    assert not t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 0
    assert t_solver.cur_assignment == []
    assert t_solver.assignments_log == [tuple()]
    assert not t_solver.is_same_rep(f_3a, f_a)
    assert not t_solver.is_same_rep(f_3a, a)
    assert t_solver.unassigned_ints == {1, 2, 3}

    t_solver.process_assignment(-3)
    assert not t_solver.check_t_propagations()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver.is_t_conflict()
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 1
    assert t_solver.cur_assignment == [-3]
    assert t_solver.assignments_log == [tuple(), (-3,)]
    assert not t_solver.is_same_rep(f_3a, a)
    assert not t_solver.is_same_rep(f_a, a)
    assert t_solver.unassigned_ints == {1, 2}

    t_solver.process_assignment(2)
    assert not t_solver.check_t_propagations()
    assert not t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 1
    assert t_solver.cur_assignment == [-3, 2]
    assert t_solver.assignments_log == [tuple(), (-3,), (-3, 2)]
    assert t_solver.is_same_rep(f_5a, a)
    assert t_solver.unassigned_ints == {1}

    t_solver.process_assignment(-1)
    assert not t_solver.check_t_propagations()
    assert not t_solver.is_t_conflict()
    assert t_solver.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver.pop_t_propagation()
    assert len(t_solver.active_neqs) == 2
    assert t_solver.cur_assignment == [-3, 2, -1]
    assert t_solver.assignments_log == [tuple(), (-3,), (-3, 2), (-3, 2, -1)]
    assert t_solver.is_same_rep(f_5a, a)
    assert t_solver.unassigned_ints == set()


def test_case2():
    x = Var("x")
    y = Var("y")
    g_x = Func("g", x)
    f_x = Func("f", x)
    f_y = Func("f", y)
    g_f_x = Func("g", f_x)
    f_g_x = Func("f", g_x)
    f_g_f_y = Func("f", Func("g", f_y))

    cnf_list_2 = [[Equal(f_g_x, g_f_x)], [Equal(f_g_f_y, x)], [Equal(f_y, x)],
                  [NEqual(g_f_x, x)]]
    abs_literals_to_ints_2 = {Equal(f_g_x, g_f_x): 1,
                              NEqual(f_g_x, g_f_x): -1,
                              Equal(f_g_f_y, x): 2,
                              NEqual(f_g_f_y, x): -2,
                              Equal(f_y, x): 3,
                              NEqual(f_y, x): -3,
                              Equal(g_f_x, x): 4,
                              NEqual(g_f_x, x): -4
                              }

    t_solver_2 = UFTheory()
    t_solver_2.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_2.items()})

    t_solver_2.process_assignment(1)
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT

    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 0
    assert t_solver_2.cur_assignment == [1]
    assert t_solver_2.assignments_log == [tuple(), (1,)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.unassigned_ints == {2, 3, 4}

    t_solver_2.process_assignment(2)
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 0
    assert t_solver_2.cur_assignment == [1, 2]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.unassigned_ints == {3, 4}

    t_solver_2.process_assignment(-4)
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 1
    assert t_solver_2.cur_assignment == [1, 2, -4]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2), (1, 2, -4)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.unassigned_ints == {3}

    t_solver_2.process_assignment(3)
    assert not t_solver_2.check_t_propagations()
    assert t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability() == (ResultCode.UNSAT,
                                                   {-1, -2, 4, -3})
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 1
    assert t_solver_2.cur_assignment == [1, 2, -4, 3]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2), (1, 2, -4),
                                          (1, 2, -4, 3)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.is_same_rep(f_g_f_y, f_y)
    assert t_solver_2.unassigned_ints == set()

    t_solver_2.conflict_recovery([1, 2])
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 0
    assert t_solver_2.cur_assignment == [1, 2]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.unassigned_ints == {3, 4}

    t_solver_2.process_assignment(-3)
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 1
    assert t_solver_2.cur_assignment == [1, 2, -3]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2), (1, 2, -3)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.unassigned_ints == {4}

    t_solver_2.process_assignment(4)
    assert not t_solver_2.check_t_propagations()
    assert not t_solver_2.is_t_conflict()
    assert t_solver_2.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_2.pop_t_propagation()
    assert len(t_solver_2.active_neqs) == 1
    assert t_solver_2.cur_assignment == [1, 2, -3, 4]
    assert t_solver_2.assignments_log == [tuple(), (1,), (1, 2), (1, 2, -3),
                                          (1, 2, -3, 4)]
    assert t_solver_2.is_same_rep(f_g_x, g_f_x)
    assert t_solver_2.is_same_rep(f_g_f_y, x)
    assert t_solver_2.unassigned_ints == set()


def test_case3():
    a = Var("a")
    c = Var("c")
    d = Var("d")
    g_a = Func("g", a)
    f_c = Func("f", c)
    f_g_a = Func("f", g_a)
    cnf_list_3 = [[Equal(g_a, c)], [NEqual(f_g_a, f_c), Equal(g_a, d)], [NEqual(c, d)]]
    abs_literals_to_ints_3 = {Equal(g_a, c): 1,
                              NEqual(g_a, c): -1,
                              Equal(f_g_a, f_c): 2,
                              NEqual(f_g_a, f_c): -2,
                              Equal(g_a, d): 3,
                              NEqual(g_a, d): -3,
                              Equal(c, d): 4,
                              NEqual(c, d): -4
                              }

    t_solver_3 = UFTheory()
    t_solver_3.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_3.items()})

    t_solver_3.process_assignment(1)
    assert t_solver_3.check_t_propagations()
    assert not t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability()[0] == ResultCode.SAT
    assert t_solver_3.pop_t_propagation() == 2
    assert len(t_solver_3.active_neqs) == 0
    assert t_solver_3.cur_assignment == [1]
    assert t_solver_3.assignments_log == [tuple(), (1,)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.unassigned_ints == {2, 3, 4}

    t_solver_3.process_assignment(-2)
    assert not t_solver_3.check_t_propagations()
    assert t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability() == (ResultCode.UNSAT, {-1, 2})
    assert not t_solver_3.pop_t_propagation()
    assert len(t_solver_3.active_neqs) == 1
    assert t_solver_3.cur_assignment == [1, -2]
    assert t_solver_3.assignments_log == [tuple(), (1,), (1, -2)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.unassigned_ints == {3, 4}

    t_solver_3.conflict_recovery([1])
    assert t_solver_3.check_t_propagations()
    assert not t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_3.t_propagations_queue) == [2]
    assert len(t_solver_3.active_neqs) == 0
    assert t_solver_3.cur_assignment == [1]
    assert t_solver_3.assignments_log == [tuple(), (1,)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.unassigned_ints == {2, 3, 4}

    t_solver_3.process_assignment(3)
    assert t_solver_3.check_t_propagations()
    assert not t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_3.t_propagations_queue) == [2, 4]
    assert len(t_solver_3.active_neqs) == 0
    assert t_solver_3.cur_assignment == [1, 3]
    assert t_solver_3.assignments_log == [tuple(), (1,), (1, 3)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.is_same_rep(c, d)
    assert t_solver_3.unassigned_ints == {2, 4}

    t_solver_3.process_assignment(2)
    assert t_solver_3.check_t_propagations()
    assert not t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_3.t_propagations_queue) == [4]
    assert len(t_solver_3.active_neqs) == 0
    assert t_solver_3.cur_assignment == [1, 3, 2]
    assert t_solver_3.assignments_log == [tuple(), (1,), (1, 3), (1, 3, 2)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.is_same_rep(c, d)
    assert t_solver_3.unassigned_ints == {4}

    t_solver_3.process_assignment(4)
    assert not t_solver_3.check_t_propagations()
    assert not t_solver_3.is_t_conflict()
    assert t_solver_3.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_3.t_propagations_queue
    assert len(t_solver_3.active_neqs) == 0
    assert t_solver_3.cur_assignment == [1, 3, 2, 4]
    assert t_solver_3.assignments_log == [tuple(), (1,), (1, 3), (1, 3, 2),
                                          (1, 3, 2, 4)]
    assert t_solver_3.is_same_rep(g_a, c)
    assert t_solver_3.is_same_rep(f_g_a, f_c)
    assert not t_solver_3.is_same_rep(f_g_a, c)
    assert t_solver_3.is_same_rep(c, d)
    assert t_solver_3.unassigned_ints == set()


# test case functions with arity = 2
def test_case4():
    a = Var("a")
    b = Var("b")
    c = Var("c")
    f_ab = Func("f", [a, b])
    f_bc = Func("f", [b, c])
    g_bc = Func("g", [b, c])
    f_fab_b = Func("f", [f_ab, b])
    g_fab_fbc = Func("g", [f_ab, f_bc])
    cnf_list_4 = [[Equal(a, b), Equal(b, c)], [Negate(c), Equal(f_ab, f_bc),
                                         Equal(b, f_ab), NEqual(c, f_bc)],
                  [Equal(g_fab_fbc, g_bc), NEqual(c, f_ab), Equal(b, f_bc)],
                  [Equal(f_fab_b, g_fab_fbc)]]
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

    t_solver_4 = UFTheory()
    t_solver_4.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_4.items()})


    # check a=b ^ b=c --> f(a,b) = f(b,c)
    t_solver_4.process_assignment(1)
    t_solver_4.process_assignment(2)
    assert t_solver_4.check_t_propagations()
    assert not t_solver_4.is_t_conflict()
    assert t_solver_4.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_4.t_propagations_queue) == [4]
    assert len(t_solver_4.active_neqs) == 0
    assert t_solver_4.cur_assignment == [1, 2]
    assert t_solver_4.assignments_log == [tuple(), (1,), (1, 2)]
    assert t_solver_4.is_same_rep(a, c)
    assert t_solver_4.is_same_rep(f_ab, f_bc)
    assert t_solver_4.unassigned_ints == {3, 4, 5, 6, 7, 8, 9, 10}

    # check f=(a,b) ^ c=f(b,c) --> g(f(a,b), f(b,c)) = g(b,c)
    t_solver_4.conflict_recovery([])
    t_solver_4.process_assignment(6)
    assert not t_solver_4.check_t_propagations()
    t_solver_4.process_assignment(5)
    assert t_solver_4.check_t_propagations()
    assert not t_solver_4.is_t_conflict()
    assert t_solver_4.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_4.t_propagations_queue) == [7]
    assert len(t_solver_4.active_neqs) == 0
    assert t_solver_4.cur_assignment == [6, 5]
    assert t_solver_4.assignments_log == [tuple(), (6,), (6, 5)]
    assert t_solver_4.is_same_rep(b, f_ab)
    assert t_solver_4.is_same_rep(c, f_bc)
    assert not t_solver_4.is_same_rep(b, c)
    assert t_solver_4.is_same_rep(g_fab_fbc, g_bc)
    assert t_solver_4.unassigned_ints == {3, 4, 1, 2, 7, 8, 9, 10}

    # check c=f(a,b) ^ b = f(b,c) not implies g(f(a,b),f(b,c)) = g(b, c)
    # (wrong order)
    t_solver_4.conflict_recovery([])
    t_solver_4.process_assignment(9)
    t_solver_4.process_assignment(8)
    assert not t_solver_4.check_t_propagations()
    assert not t_solver_4.is_t_conflict()
    assert t_solver_4.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_4.t_propagations_queue
    assert len(t_solver_4.active_neqs) == 0
    assert t_solver_4.cur_assignment == [9, 8]
    assert t_solver_4.assignments_log == [tuple(), (9,), (9, 8)]
    assert not t_solver_4.is_same_rep(g_fab_fbc, g_bc)
    assert t_solver_4.unassigned_ints == {3, 4, 1, 2, 7, 5, 6, 10}

    # check b=f(b,c) not implies f(f(a,b), b) = g(f(a,b), f(b,c))
    t_solver_4.conflict_recovery([9])
    assert not t_solver_4.check_t_propagations()
    assert not t_solver_4.is_t_conflict()
    assert t_solver_4.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_4.t_propagations_queue
    assert len(t_solver_4.active_neqs) == 0
    assert t_solver_4.cur_assignment == [9]
    assert t_solver_4.assignments_log == [tuple(), (9,)]
    assert not t_solver_4.is_same_rep(g_fab_fbc, g_bc)
    assert t_solver_4.unassigned_ints == {3, 4, 1, 2, 7, 5, 6, 8, 10}


def test_case5():
    a = Var("a")
    b = Var("b")
    c = Var("c")
    s = Var("s")
    t = Var("t")
    r = Var("r")
    f_s = Func("f", s)
    f_t = Func("f", t)
    f_a = Func("f", a)
    f_c = Func("f", c)

    cnf_list_5 = [[Equal(a, b)], [NEqual(a, b), NEqual(s, t), Equal(b, c)],
                  [Equal(s, t), NEqual(t, r), Equal(f_s, f_t)],
                  [NEqual(b, c), NEqual(t, r), Equal(f_s, f_a)],
                  [NEqual(f_s, f_a), NEqual(f_a, f_c)]]
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

    t_solver_5 = UFTheory()
    t_solver_5.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_5.items()})

    t_solver_5.process_assignment(1)
    t_solver_5.process_assignment(2)
    assert t_solver_5.check_t_propagations()
    assert not t_solver_5.is_t_conflict()
    assert t_solver_5.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_5.t_propagations_queue) == [5]
    assert len(t_solver_5.active_neqs) == 0
    assert t_solver_5.cur_assignment == [1, 2]
    assert t_solver_5.assignments_log == [tuple(), (1,), (1, 2)]
    assert t_solver_5.is_same_rep(a, b)
    assert t_solver_5.is_same_rep(s, t)
    assert not t_solver_5.is_same_rep(s, a)
    assert t_solver_5.is_same_rep(f_s, f_t)
    assert t_solver_5.unassigned_ints == {3, 4, 5, 6, 7}

    t_solver_5.process_assignment(3)
    assert t_solver_5.check_t_propagations()
    assert not t_solver_5.is_t_conflict()
    assert t_solver_5.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_5.t_propagations_queue) == [5, 7]
    assert len(t_solver_5.active_neqs) == 0
    assert t_solver_5.cur_assignment == [1, 2, 3]
    assert t_solver_5.assignments_log == [tuple(), (1,), (1, 2), (1, 2, 3)]
    assert t_solver_5.is_same_rep(a, b)
    assert t_solver_5.is_same_rep(s, t)
    assert not t_solver_5.is_same_rep(s, a)
    assert t_solver_5.is_same_rep(f_s, f_t)
    assert t_solver_5.unassigned_ints == {4, 5, 6, 7}

    t_solver_5.process_assignment(4)
    t_solver_5.process_assignment(6)
    t_solver_5.process_assignment(-7)
    assert t_solver_5.check_t_propagations()
    assert t_solver_5.is_t_conflict()
    assert t_solver_5.analyze_satisfiability() == (ResultCode.UNSAT,
                                                   {-1, -3, 7})
    assert list(t_solver_5.t_propagations_queue) == [5]
    assert len(t_solver_5.active_neqs) == 1
    assert t_solver_5.cur_assignment == [1, 2, 3, 4, 6, -7]
    assert t_solver_5.assignments_log == [tuple(), (1,), (1, 2), (1, 2, 3),
                                          (1, 2, 3, 4), (1, 2, 3, 4, 6),
                                          (1, 2, 3, 4, 6, -7)]
    assert t_solver_5.is_same_rep(a, b)
    assert t_solver_5.is_same_rep(s, t)
    assert not t_solver_5.is_same_rep(s, a)
    assert t_solver_5.is_same_rep(f_s, f_t)
    assert t_solver_5.unassigned_ints == {5}

    t_solver_5.conflict_recovery([1])
    assert not t_solver_5.check_t_propagations()
    assert not t_solver_5.is_t_conflict()
    assert t_solver_5.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_5.pop_t_propagation()
    assert len(t_solver_5.active_neqs) == 0
    assert t_solver_5.cur_assignment == [1]
    assert t_solver_5.assignments_log == [tuple(), (1,)]
    assert t_solver_5.is_same_rep(a, b)
    assert not t_solver_5.is_same_rep(s, t)
    assert t_solver_5.unassigned_ints == {2, 3, 4, 5, 6, 7}


# check t_propagation of neq and combination of non eqs/neqs with eqs/neqs
def test_case6():
    a = Var("a")
    b = Var("b")
    c = Var("c")
    cnf_list_6 = [[Equal(a, b)], [NEqual(b, c)], [Equal(a, c), c]]
    abs_literals_to_ints_6 = {Equal(a, b): 1,
                              NEqual(a, b): -1,
                              Equal(b, c): 2,
                              NEqual(b, c): -2,
                              Equal(a, c): 3,
                              NEqual(a, c): -3,
                              c: 4,
                              Negate(c): -4
                              }

    t_solver_6 = UFTheory()
    t_solver_6.register_abstraction_map({v: k for (k, v) in
                                              abs_literals_to_ints_6.items()})

    t_solver_6.process_assignment(4)
    t_solver_6.process_assignment(1)
    t_solver_6.process_assignment(-2)
    assert t_solver_6.check_t_propagations()
    assert not t_solver_6.is_t_conflict()
    assert t_solver_6.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_6.t_propagations_queue) == [-3]
    assert len(t_solver_6.active_neqs) == 1
    assert t_solver_6.cur_assignment == [4, 1, -2]
    assert t_solver_6.assignments_log == [tuple(), (4,), (4, 1), (4, 1, -2)]
    assert t_solver_6.is_same_rep(a, b)
    assert t_solver_6.unassigned_ints == {3}

    t_solver_6.conflict_recovery([])
    t_solver_6.process_assignment(-4)
    assert not t_solver_6.check_t_propagations()
    assert not t_solver_6.is_t_conflict()
    assert t_solver_6.analyze_satisfiability()[0] == ResultCode.SAT
    assert not t_solver_6.check_t_propagations()
    assert len(t_solver_6.active_neqs) == 1
    assert t_solver_6.cur_assignment == [-4]
    assert t_solver_6.assignments_log == [tuple(), (-4,)]
    assert not t_solver_6.is_same_rep(a, b)

    t_solver_6.process_assignment(1)
    t_solver_6.process_assignment(-2)
    assert t_solver_6.check_t_propagations()
    assert not t_solver_6.is_t_conflict()
    assert t_solver_6.analyze_satisfiability()[0] == ResultCode.SAT
    assert list(t_solver_6.t_propagations_queue) == [-3]
    assert len(t_solver_6.active_neqs) == 2
    assert t_solver_6.cur_assignment == [-4, 1, -2]
    assert t_solver_6.assignments_log == [tuple(), (-4,), (-4, 1), (-4, 1, -2)]
    assert t_solver_6.is_same_rep(a, b)
    assert t_solver_6.unassigned_ints == {3}

    t_solver_6.process_assignment(3)
    assert not t_solver_6.check_t_propagations()
    assert t_solver_6.is_t_conflict()
