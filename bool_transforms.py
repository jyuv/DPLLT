from __future__ import annotations
from logical_blocks import Atom, Var, Equiv, Imply, BinaryOp, UnaryOp, \
    Negate, Or, And, NEqual, Equal, Func


def _reduce_to_basic(node: Atom) -> Atom:
    if not node.is_literal():
        if isinstance(node, Equiv) or isinstance(node, Imply):
            node = node.to_basic()

        if isinstance(node, BinaryOp):
            node.left = _reduce_to_basic(node.left)
            node.right = _reduce_to_basic(node.right)

        elif isinstance(node, UnaryOp):
            node.item = _reduce_to_basic(node.item)
    return node


def _organize_negations(node: Atom) -> Atom:
    if not node.is_literal():
        if isinstance(node, Negate):
            node = node.item.negate()

        if isinstance(node, BinaryOp):
            node.left = _organize_negations(node.left)
            node.right = _organize_negations(node.right)
        elif isinstance(node, UnaryOp):
            node = _organize_negations(node)
    return node


def _nnf_to_cnf(node: Atom) -> Atom:
    if not node.is_literal():
        if isinstance(node, Or):
            node = node.cnf_distribute()

        if isinstance(node, BinaryOp):
            node.left = _nnf_to_cnf(node.left)
            node.right = _nnf_to_cnf(node.right)
        elif isinstance(node, UnaryOp):
            node.item = _nnf_to_cnf(node.item)
    elif isinstance(node, Negate):
        if isinstance(node.item, Equal):
            return NEqual(node.item.left, node.item.right)
        elif isinstance(node.item, NEqual):
            return Equal(node.item.left, node.item.right)
    return node


def to_nnf(node: Atom) -> Atom:
    return _organize_negations(_reduce_to_basic(node))


def to_cnf(node: Atom) -> Atom:
    return _nnf_to_cnf((to_nnf(node)))


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


def _add_and_cnf(equivs_conjunction, f_rep, left_rep, right_rep):
    equivs_conjunction.append(Equiv(f_rep, And(left_rep, right_rep)))


def _add_or_cnf(equivs_conjunction, f_rep, left_rep, right_rep):
    equivs_conjunction.append(Equiv(f_rep, Or(left_rep, right_rep)))


def _add_equiv_cnf(equivs_conjunction, f_rep, left_rep, right_rep):
    equivs_conjunction.append(Equiv(f_rep, Equiv(left_rep, right_rep)))


def _add_imply_cnf(equivs_conjunction, f_rep, left_rep, right_rep):
    equivs_conjunction.append(Equiv(f_rep, Imply(left_rep, right_rep)))


def _handle_binary(f, equivs_conjunction, f_rep, left_rep, right_rep):
    if isinstance(f, And):
        _add_and_cnf(equivs_conjunction, f_rep, left_rep, right_rep)
    elif isinstance(f, Or):
        _add_or_cnf(equivs_conjunction, f_rep, left_rep, right_rep)
    elif isinstance(f, Equiv):
        _add_equiv_cnf(equivs_conjunction, f_rep, left_rep, right_rep)
    elif isinstance(f, Imply):
        _add_imply_cnf(equivs_conjunction, f_rep, left_rep, right_rep)
    else:
        raise ValueError("Unrecognized type of f: {0}".format(type(f)))


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

        _handle_binary(f, equivs_conjunction, dummy_tracker.get_dummy(f),
                       left_rep, right_rep)

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
