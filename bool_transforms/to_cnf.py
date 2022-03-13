from parsing.logical_blocks import Atom, Equiv, Imply, BinaryOp, UnaryOp, Negate, Or, \
    Equal, NEqual, Less, Geq


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
        elif isinstance(node.item, Less):
            return Geq(node.item.a, node.item.b)
        elif isinstance(node.item, Geq):
            return Less(node.item.a, node.item.b)
    return node


def to_nnf(node: Atom) -> Atom:
    return _organize_negations(_reduce_to_basic(node))


def to_cnf(node: Atom) -> Atom:
    return _nnf_to_cnf((to_nnf(node)))