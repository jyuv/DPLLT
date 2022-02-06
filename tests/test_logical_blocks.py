from logical_blocks import Var, Negate, Imply, Equiv, And, Or

x1 = Var("X1")
x2 = Var("X2")
x3 = Var("X3")
x4 = Var("X4")

f1 = Negate(Imply(x1, And(x1, x2)))  # (x1 -> (x1 & x2))
f2 = Negate(Equiv(x1, And(x1, x2)))  # (x1 <-> (x1 & x2))
f3 = And(Or(x1, Negate(x2)), Imply(x3, x2))  # (x1 || -x2) & (x3 -> x2)


def test_is_literal():
    atoms = [x1, Negate(x1), Negate(Negate(x1)), Imply(Negate(x1), x2),
             Equiv(x2, x3), And(x2, x3), Or(And(x1, x2), x3)]
    atoms_is_literals = [a.is_literal() for a in atoms]
    assert atoms_is_literals == [True, True, False, False, False, False, False]


def test_print():
    expected_1 = "!(X1->(X1&X2))"
    expected_2 = "!(X1<->(X1&X2))"
    expected_3 = "((X1|!X2)&(X3->X2))"
    assert str(f1).replace(" ", "") == expected_1
    assert str(f2).replace(" ", "") == expected_2
    assert str(f3).replace(" ", "") == expected_3


def test_negations():
    assert Negate(x1).negate() == x1
    assert Negate(Negate(x2)).negate() == Negate(x2)

    assert And(x1, x2).negate() == Or(Negate(x1), Negate(x2))
    assert And(Negate(x1), x2).negate() == Or(Negate(Negate(x1)), Negate(x2))

    assert Or(x1, x2).negate() == And(Negate(x1), Negate(x2))
    assert Or(Negate(Negate(x1)), Negate(x2)).negate() == And(Negate(Negate(Negate(x1))),
                                                              Negate(Negate(x2)))


def test_to_basic():
    assert Imply(x1, x2).to_basic() == Or(Negate(x1), x2)
    assert Imply(Negate(x1), Negate(x2)).to_basic() == Or(Negate(Negate(x1)), Negate(x2))
    assert Imply(And(x1, x2), x3).to_basic() == Or(Negate(And(x1, x2)), x3)

    assert Equiv(x1, x2).to_basic() == And(Or(Negate(x1), x2), Or(Negate(x2), x1))
    assert Equiv(Negate(x1), Negate(x2)).to_basic() == And(Or(Negate(Negate(x1)), Negate(x2)),
                                                     Or(Negate(Negate(x2)), Negate(x1)))
    assert Equiv(And(x1, x2), x3).to_basic() == And(Or(Negate(And(x1, x2)), x3),
                                                    Or(Negate(x3), And(x1, x2)))


def test_cnf_distribute():
    assert Or(x1, x2).cnf_distribute() == Or(x1, x2)
    assert Or(Negate(x1), Negate(x2)).cnf_distribute() == Or(Negate(x1), Negate(x2))
    assert Or(Negate(Negate(x1)), Negate(x2)).cnf_distribute() == Or(Negate(Negate(x1)),
                                                            Negate(x2))

    assert Or(And(x1, x2), x3).cnf_distribute() == And(Or(x1, x3), Or(x2, x3))
    assert Or(And(x1, x2), Negate(x3)).cnf_distribute() == And(Or(x1, Negate(x3)),
                                                            Or(x2, Negate(x3)))

    assert Or(x1, And(x2, x3)).cnf_distribute() == And(Or(x1, x2), Or(x1, x3))
    assert Or(Negate(x1), And(x2, x3)).cnf_distribute() == And(Or(Negate(x1), x2),
                                                            Or(Negate(x1), x3))

    assert Or(Negate(And(x1, x2)), Negate(x3)).cnf_distribute() == Or(Negate(And(x1,
                                                                        x2)),
                                                                Negate(x3))
    assert Or(Negate(x3), Negate(And(x1, x2))).cnf_distribute() == Or(Negate(x3),
                                                                Negate(And(x1,
                                                                        x2)))

    assert Or(And(x1, x2), And(x3, x4)).cnf_distribute() == And(Or(x1, x3),
                                                                And(
                                                                    Or(x1, x4),
                                                                    And(
                                                                        Or(x2,
                                                                           x3),
                                                                        Or(x2,
                                                                           x4)
                                                                        )
                                                                    )
                                                                )
