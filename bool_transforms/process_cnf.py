"""
General Notes
-------------
A module composed of methods to process CNF formulas. The main method abstracts
a formula of logical blocks into a list of sets of ints, where each number i
represent a literal and -i represents its negation.

The module also provides a processing for simplifying negations in equalities
and functions arguments.

"""

from typing import List, Dict, Set, Union, Tuple
from parsing.logical_blocks import Var, Atom, BinaryOp, UnaryOp, Or, And,\
    Negate, NEqual, Equal, Func, Less, Geq

from bool_transforms.tseitin_transform import tseitin_transform,\
    DummyVarsTracker


def get_nested_literals(node: Atom, output_set: Set[Atom]) -> None:
    """
    Add all nested literals in the node formula into output_set
    :param node: root of formula to extract nested literals from
    :param output_set: the set to add the nested literals to
    """
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
    """
    Recursive method for extracting literals from a CNF logical formula
    into a list where each clause in the formula is represented by a set of
    literals which are part of it.
    :param node: The root of the logical formula to be processed
    :param out_list: The list to export sets of literals to
    """
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
    """
    Creates a mapping of logical literals to int values. The mapping is created
    as for each literal mapped to i, its negation is mapped to -i.
    :param literals: Set of literals to be mapped
    :return: A mapping of literals to ints
    """
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


def to_equalities_with_no_negations_args(node: Union[Equal, NEqual]) -> Atom:
    """
    Convert formula rooted in node to a formula with no negated args in
    equalities and inequalities.
    This is done by counting the number of negations and convert = -> !=
    and != -> if number of negations is odd
    :param node: The root of the given formula to convert
    :return: The root of the converted formula
    """
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


def _remove_negations_in_eqs_helper(node: Atom) -> Atom:
    """
    A recursive helper method to remove negations in =, != arguments
    :param node: A root logical atom of the formula to be processed
    :return: The root of the formula with no negations in =, != args
    """
    if isinstance(node, Equal) or isinstance(node, NEqual):
        return to_equalities_with_no_negations_args(node)

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


def _remove_negations_in_eqs(cnf_conjunction: List[Atom]) -> List[Atom]:
    """
    A method that convert a list of logical formulas root to a list of
    clauses roots with no negations in =, != args
    :param cnf_conjunction: A list of logical formulas roots
    :return: A list with equivalant formulas as in the input only with no
    negations in =, != args
    """
    new_clauses = []
    for clause in cnf_conjunction:
        new_clauses.append(_remove_negations_in_eqs_helper(clause))
    return new_clauses


def _remove_negations_in_func_args_helper(f: Atom,
                                          to_add_neqs: Dict[NEqual, None],
                                          dvar_tracker: DummyVarsTracker,
                                          dummy_map: Dict[Var, Negate]) -> Atom:
    """
    Recursive helper for removing negations in functions arguments
    :param f: root of logical formula to be processed
    :param to_add_neqs: A dictionary served as an ordered set of NEquals added
                        during preprocessing.
    :param dvar_tracker: DummyVarsTracker to produce dummy vars if necessary
    :param dummy_map: Mapping of dummy vars added to the original variables
    :return: The root of the processed logical formula
    """
    if isinstance(f, BinaryOp):
        f.left = _remove_negations_in_func_args_helper(f.left, to_add_neqs,
                                                       dvar_tracker, dummy_map)
        f.right = _remove_negations_in_func_args_helper(f.right, to_add_neqs,
                                                        dvar_tracker, dummy_map)
        return f

    elif isinstance(f, UnaryOp):
        f.item = _remove_negations_in_func_args_helper(f.item, to_add_neqs,
                                                       dvar_tracker, dummy_map)
        return f

    elif isinstance(f, Func):
        new_args = []
        for arg in f.args:
            if isinstance(arg, Negate):
                new_var = dvar_tracker.get_dummy(arg)
                dummy_map[new_var] = arg
                to_add_neqs[NEqual(arg.item, new_var)] = None
                arg = new_var

            elif isinstance(arg, Func):
                arg = _remove_negations_in_func_args_helper(arg, to_add_neqs,
                                                            dvar_tracker,
                                                            dummy_map)
            new_args.append(arg)
        return Func(f.name, new_args)

    else:
        return f


def _remove_negations_in_func_args(tseitin_clauses: List[Atom]) ->\
        Tuple[List[Atom], Dict[Var, NEqual]]:
    """
    Removes negations from functions args in each of the given clauses
    :param tseitin_clauses: List of roots of formulas, each representing
    a tseitin clause
    :return: A Tuple of the processed clauses list and a mapping of dummy vars
    added to the original expressions they replaced.
    """
    to_add_neqs = dict()  # used as ordered set
    dummy_map = dict()
    dummy_var_tracker = DummyVarsTracker(init_name="#N")

    for i in range(len(tseitin_clauses)):
        cur_cl = tseitin_clauses[i]
        tseitin_clauses[i] = _remove_negations_in_func_args_helper(
            cur_cl, to_add_neqs, dummy_var_tracker, dummy_map)

    to_add_neqs = list(to_add_neqs.keys())
    tseitin_clauses.extend(to_add_neqs)

    return tseitin_clauses, dummy_map


def _cnf_conjunction_to_ints(cnf_conjunction: List[Atom]) ->\
        Tuple[List[Set[int]], Dict[Atom, int]]:
    """
    converts a list of logical formulas' roots representing a cnf conjunction
    into a list of sets of ints which is equivalent.
    :param cnf_conjunction: A list of roots of logical formulas' roots
    :return: A tuple of the ints version of the formula and the mapping
    of logical literals to ints that was used for the conversion.
    """
    # First - collect literals appearing and create a mapping
    literals = set()
    for clause in cnf_conjunction:
        get_nested_literals(clause, literals)
    lit_mapping = _create_literals_mapping(literals)
    conj_with_ints = []
    new_conj = []
    for root in cnf_conjunction:  # make new_conj into a list of sets of clauses
        _reformat_cnf_helper(root, new_conj)
    for cl in new_conj:  # translate the clauses to int format using the mapping
        cur_clause_ints = set()
        for lit in cl:
            cur_clause_ints.add(lit_mapping[lit])
        conj_with_ints.append(cur_clause_ints)
    return conj_with_ints, lit_mapping


def to_abstract_cnf_conjunction(raw_formula: Atom) ->\
        Tuple[List[Set[int]], Dict[int, Atom], Dict[Var, Atom]]:
    """
    Abstracts a logical formula to a CNF conjunction of clauses where each
    clause is represented by a set of int where each int representing a literal
    and its negation is the representation of the literal's negation
    :param raw_formula: The original logical formula to be processed
    :return: A tuple of 3 elements:
            - The new abstracted cnf conjunction version of raw_formula
              it's represented as a list of sets of ints where each int
              represents a literal and each set represents a clause.
            - A dictionary mapping the ints to the literals they're representing
            - A dictionary mapping dummy variables to atoms in the raw_formula
    """
    cnf_conjunction = tseitin_transform(raw_formula)

    # preprocess negations
    cnf_conjunction = _remove_negations_in_eqs(cnf_conjunction)
    cnf_conjunction, dummy_map = _remove_negations_in_func_args(cnf_conjunction)

    int_cnf_formula, lit_to_int = _cnf_conjunction_to_ints(cnf_conjunction)

    # remove trivial clauses
    int_cnf_formula = [clause for clause in int_cnf_formula if
                       len({abs(lit) for lit in clause}) == len(clause)]

    abstraction_map = {v: k for (k, v) in lit_to_int.items()}

    return int_cnf_formula, abstraction_map, dummy_map
