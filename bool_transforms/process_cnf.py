from typing import List, Dict, Set
from parsing.logical_blocks import Var, Atom, BinaryOp, UnaryOp, Or, And,\
    Negate, NEqual, Equal, Func, Less, Geq

from bool_transforms.tseitin_transform import tseitin_transform


def get_nested_literals(node: Atom, output_set: Set[Atom]) -> None:
    if not node.is_literal():
        if isinstance(node, BinaryOp):
            get_nested_literals(node.left, output_set)
            get_nested_literals(node.right, output_set)
        elif isinstance(node, UnaryOp):
            get_nested_literals(node.item, output_set)
    else:
        output_set.add(node)


# Assumes only Or, And, and literals exists
def _reformat_cnf_helper(node: Atom, out_list: List[Set[Atom]]) -> None:
    if not node.is_literal():
        if isinstance(node, Or):
            temp = set()
            get_nested_literals(node, temp)
            out_list.append(temp)
        elif isinstance(node, And):
            _reformat_cnf_helper(node.left, out_list)
            _reformat_cnf_helper(node.right, out_list)
    else:
        out_list.append({node})


def _create_literals_mapping(literals: Set[Atom]) -> Dict[Atom, int]:
    lits_encountered = dict()  # dict that will be used as an ordered set
    for lit in literals:
        if isinstance(lit, Var) or isinstance(lit, Func) or isinstance(lit,
                                                                       Equal):
            lits_encountered[lit] = None
        elif isinstance(lit, Negate):
            if isinstance(lit.item, Less):
                lits_encountered[lit.item.negate()] = None
            else:
                lits_encountered[lit.item] = None
        elif isinstance(lit, NEqual):
            lits_encountered[Equal(lit.left, lit.right)] = None
        elif isinstance(lit, Less):
            lits_encountered[Geq(lit.left, lit.right)] = None

    lits_encountered = list(lits_encountered.keys())
    mapping = {old_name: idx + 1 for (idx, old_name) in
               enumerate(lits_encountered)}
    for lit in lits_encountered:
        if isinstance(lit, Var) or isinstance(lit, Func):
            mapping[Negate(lit)] = -mapping[lit]
        elif isinstance(lit, Equal):
            mapping[NEqual(lit.left, lit.right)] = -mapping[lit]
        elif isinstance(lit, Geq):
            mapping[Less(lit.left, lit.right)] = -mapping[lit]
    return mapping


def _remove_negations_in_eqs_helper(node):
    if isinstance(node, Equal) or isinstance(node, NEqual):
        num_of_negs = 0
        if isinstance(node.left, Negate):
            node.left = node.left.item
            num_of_negs += 1
        if isinstance(node.right, Negate):
            node.right = node.right.item
            num_of_negs += 1

        if num_of_negs % 2 == 1:
            if isinstance(node, Equal):
                return NEqual(node.left, node.right)
            else:
                return Equal(node.left, node.right)
        else:
            return node

    elif node.is_literal():
        return node
    elif isinstance(node, BinaryOp):
        left = _remove_negations_in_eqs_helper(node.left)
        right = _remove_negations_in_eqs_helper(node.right)
        node.left = left
        node.right = right
        return node
    elif isinstance(node, UnaryOp):
        return _remove_negations_in_eqs_helper(node)


def _remove_negations_in_eqs(cnf_conjunction):
    new_clauses = []
    for clause in cnf_conjunction:
        new_clauses.append(_remove_negations_in_eqs_helper(clause))
    return new_clauses


def _cnf_conjunction_to_ints(cnf_conjunction: List[Atom]):
    literals = set()
    for clause in cnf_conjunction:
        get_nested_literals(clause, literals)
    lit_mapping = _create_literals_mapping(literals)
    conj_with_ints = []
    new_conj = []
    for root in cnf_conjunction:
        _reformat_cnf_helper(root, new_conj)
    for cl in new_conj:
        cur_clause_ints = set()
        for lit in cl:
            cur_clause_ints.add(lit_mapping[lit])
        conj_with_ints.append(cur_clause_ints)
    return conj_with_ints, lit_mapping


def to_abstract_cnf_conjunction(raw_formula):
    cnf_conjunction = tseitin_transform(raw_formula)
    cnf_conjunction = _remove_negations_in_eqs(cnf_conjunction)
    int_cnf_formula, lit_to_int = _cnf_conjunction_to_ints(cnf_conjunction)

    # remove trivial clauses
    int_cnf_formula = [clause for clause in int_cnf_formula if
                       len({abs(lit) for lit in clause}) == len(clause)]

    return int_cnf_formula, {v: k for (k, v) in lit_to_int.items()}
