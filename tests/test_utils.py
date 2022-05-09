from parsing.logical_blocks import (
    Negate,
    Or,
    And,
    BinaryOp,
    NEqual,
    Less,
    Equiv,
    Imply,
    UnaryOp,
)


def verify_abstracted_assignment(formula, solution):
    if solution is None:
        return False

    # check if there is assignment for both literal and its negations
    if len({-int_lit for int_lit in solution}.intersection(solution)) > 0:
        return False

    for clause in formula:
        is_clause_satisfied = False
        for int_lit in clause:
            if int_lit < 0 and solution.get(-int_lit, None) is False:
                is_clause_satisfied = True
                break
            elif int_lit > 0 and solution.get(int_lit, None):
                is_clause_satisfied = True
                break

        if not is_clause_satisfied:
            return False

    return True


def _verify_unabstracted_assignment_helper(original_formula, assignment_map):
    if isinstance(original_formula, BinaryOp):
        left, right = original_formula.left, original_formula.right
        left_bool_val = _verify_unabstracted_assignment_helper(left, assignment_map)
        right_bool_val = _verify_unabstracted_assignment_helper(right, assignment_map)

        if isinstance(original_formula, And):
            if left_bool_val is None or right_bool_val is None:
                return None
            else:
                return left_bool_val and right_bool_val

        elif isinstance(original_formula, Or):
            if left_bool_val or right_bool_val:
                return True
            elif left_bool_val is None or right_bool_val is None:
                return None
            else:
                return False

        elif isinstance(original_formula, Imply):
            if (right_bool_val is True) or (left_bool_val is False):
                return True
            elif left_bool_val is None or right_bool_val is None:
                return None
            else:
                return False

        elif isinstance(original_formula, Equiv):
            if left_bool_val is None or right_bool_val is None:
                return None
            else:
                return left_bool_val == right_bool_val

        else:
            raise NotImplementedError(
                f"Handling type {type(original_formula)}" f" wasn't implemented"
            )

    elif isinstance(original_formula, UnaryOp):
        inner_item = original_formula.item

        if isinstance(original_formula, Negate):
            bool_val = _verify_unabstracted_assignment_helper(
                inner_item, assignment_map
            )
            if bool_val is None:
                return None
            else:
                return not bool_val

        else:
            raise NotImplementedError(
                f"Handling type {type(original_formula)}" f" wasn't implemented"
            )

    elif isinstance(original_formula, (NEqual, Less)):
        bool_val = assignment_map.get(original_formula.negate(), None)
        return None if bool_val is None else not bool_val

    else:
        return assignment_map.get(original_formula, None)


def verify_unabstracted_assignment(original_formula, assignment_map):
    if isinstance(original_formula, BinaryOp):
        left, right = original_formula.left, original_formula.right
        left_bool_val = _verify_unabstracted_assignment_helper(left, assignment_map)
        right_bool_val = _verify_unabstracted_assignment_helper(right, assignment_map)

        if isinstance(original_formula, And):
            return left_bool_val and right_bool_val

        elif isinstance(original_formula, Or):
            return left_bool_val or right_bool_val

        elif isinstance(original_formula, Imply):
            return (right_bool_val is True) or (left_bool_val is False)

        elif isinstance(original_formula, Equiv):
            if left_bool_val is None or right_bool_val is None:
                return False
            else:
                return left_bool_val == right_bool_val

        else:
            raise NotImplementedError(
                f"Handling type {type(original_formula)}" f" wasn't implemented"
            )

    elif isinstance(original_formula, UnaryOp):
        inner_item = original_formula.item
        if isinstance(original_formula, Negate):
            bool_val = _verify_unabstracted_assignment_helper(
                inner_item, assignment_map
            )
            return False if bool_val is None else not bool_val

        else:
            raise NotImplementedError(
                f"Handling type {type(original_formula)}" f" wasn't implemented"
            )

    else:
        bool_val = _verify_unabstracted_assignment_helper(
            original_formula, assignment_map
        )
        return False if bool_val is None else bool_val
