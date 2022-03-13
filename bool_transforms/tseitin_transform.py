from __future__ import annotations
from parsing.logical_blocks import Var, Equiv, Imply, BinaryOp, UnaryOp, \
    Negate, Or, And, NEqual, Func
from bool_transforms.to_cnf import to_cnf


class DummyVarsTracker:
    def __init__(self, init_name="#G"):
        self.next_dummy_id = 0
        self.dummy_map = dict()
        self.init_name = init_name

    def get_dummy(self, f):
        if f not in self.dummy_map.keys():
            new_dummy = Var(self.init_name + str(self.next_dummy_id))
            self.next_dummy_id += 1
            self.dummy_map[f] = new_dummy
        return self.dummy_map[f]


def _get_tseitin_equivs(f):
    equivs_conjunction = []
    dummy_tracker = DummyVarsTracker()
    if f.is_literal():
        return [f]
    else:
        whole_var = dummy_tracker.get_dummy(f)
        equivs_conjunction.append(whole_var)
        _tseitin_helper(f, equivs_conjunction, dummy_tracker)
    return equivs_conjunction


def _tseitin_helper(f, equivs_conjunction, dummy_tracker):
    if isinstance(f, BinaryOp):
        is_left_lit, is_right_lit = [item.is_literal() for item in
                                     (f.left, f.right)]
        left_rep = f.left if is_left_lit else dummy_tracker.get_dummy(f.left)
        right_rep = f.right if is_right_lit else \
            dummy_tracker.get_dummy(f.right)

        if isinstance(f, (And, Or, Equiv, Imply)):
            equivs_conjunction.append(Equiv(dummy_tracker.get_dummy(f),
                                            type(f)(left_rep, right_rep)))
        else:
            raise ValueError("Unrecognized type of f: {0}".format(type(f)))

        if not is_left_lit:
            _tseitin_helper(f.left, equivs_conjunction, dummy_tracker)
        if not is_right_lit:
            _tseitin_helper(f.right, equivs_conjunction, dummy_tracker)

    elif isinstance(f, Negate):
        if not f.item.is_literal():
            dummy_var = dummy_tracker.get_dummy(f.item)
            equivs_conjunction.append(Equiv(dummy_tracker.get_dummy(f),
                                            Negate(dummy_var)))
            _tseitin_helper(f.item, equivs_conjunction, dummy_tracker)
        else:
            equivs_conjunction.append(Equiv(dummy_tracker.get_dummy(f),
                                            Negate(f.item)))


def _remove_negations_in_args_helper(f, to_add_neqs, dvar_tracker):
    if isinstance(f, BinaryOp):
        f.left = _remove_negations_in_args_helper(f.left, to_add_neqs,
                                                  dvar_tracker)
        f.right = _remove_negations_in_args_helper(f.right, to_add_neqs,
                                                   dvar_tracker)
        return f

    elif isinstance(f, UnaryOp):
        f.item = _remove_negations_in_args_helper(f.item, to_add_neqs,
                                                  dvar_tracker)
        return f

    elif isinstance(f, Func):
        new_args = []
        for arg in f.args:
            if isinstance(arg, Negate):
                new_var = dvar_tracker.get_dummy(arg)
                to_add_neqs[NEqual(arg.item, new_var)] = None
                arg = new_var

            elif isinstance(arg, Func):
                arg = _remove_negations_in_args_helper(arg, to_add_neqs,
                                                       dvar_tracker)
            new_args.append(arg)
        return Func(f.name, new_args)

    else:
        return f


def _remove_negations_in_args(f):
    to_add_neqs = dict()  # used as ordered set
    dummy_var_tracker = DummyVarsTracker(init_name="#N")
    f = _remove_negations_in_args_helper(f, to_add_neqs, dummy_var_tracker)
    to_add_neqs = list(to_add_neqs.keys())
    return f, to_add_neqs


def tseitin_transform(f):
    f, to_add_neqs = _remove_negations_in_args(f)
    cnf_conjunction = [to_cnf(x) for x in _get_tseitin_equivs(f)]
    cnf_conjunction.extend(to_add_neqs)
    return cnf_conjunction
