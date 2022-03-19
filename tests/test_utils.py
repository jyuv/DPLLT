def verify_assignment(formula, solution):
    if solution is None:
        return True
    for literal in solution:
        if -literal in solution:
            return False
    for clause in formula:
        if not any(map(lambda lit: lit in solution, clause)):
            return False
    return True

