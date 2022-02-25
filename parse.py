from dataclasses import dataclass
from enum import Enum
from collections import defaultdict
from logical_blocks import *


BLOCKS_MAP = {
    "<->": Equiv,
    "<-": Imply,
    "->": Imply,
    "&": And,
    "|": Or,
    "!": Negate,
    "<": Less,
    ">=": Geq,
    "=": Equal,
    "!=": NEqual
}


# tokens types: <->, <-, ->, &, |, !, <, >=, =, !=

class TokenType(Enum):
    BINARY_OP = 1
    UNARY_OP = 2
    VAR = 3
    FUNCTION = 4
    L_PARENTHESES = 5
    R_PARENTHESES = 6
    ARG_DELIMITER = 7
    NUM = 8
    NUM_ARRAY = 9


VALID_LEFT_INPUT_TYPES = [TokenType.VAR, TokenType.FUNCTION,
                          TokenType.R_PARENTHESES, TokenType.NUM_ARRAY]
VALID_RIGHT_INPUT_TYPES = [TokenType.VAR, TokenType.FUNCTION,
                           TokenType.L_PARENTHESES, TokenType.UNARY_OP,
                           TokenType.NUM]

INEQUALITIES_OPS_TEXTS = [">=", "<"]


@dataclass
class Token:
    text: str
    token_type: TokenType


class Tokenizer:
    def __init__(self, raw_text: str):
        self.text = raw_text.replace(" ", "")
        self.len_text = len(self.text)

        if self.len_text == 0:
            raise ValueError("Didn't received symbols at all")

        self.tokens = []
        self._create_tokens()

    def _create_tokens(self):
        i = 0
        while i < self.len_text:
            cur_char = self.text[i]

            if cur_char.isalpha():
                atom_name = cur_char
                if (i + 1) >= self.len_text:
                    self.tokens.append(Token(atom_name, TokenType.VAR))

                while (i + 1) < self.len_text:
                    if self.text[i + 1].isalnum():
                        atom_name += self.text[i + 1]
                        i += 1
                    elif self.text[i+1] == "(":
                        self.tokens.append(Token(atom_name, TokenType.FUNCTION))
                        break
                    else:
                        self.tokens.append(Token(atom_name, TokenType.VAR))
                        break

            elif cur_char.isdecimal():
                num_str = cur_char
                if (i+1) >= self.len_text:
                    self.tokens.append(Token(num_str, TokenType.NUM))

                while (i + 1) < self.len_text:
                    if self.text[i+1].isdecimal():
                        num_str += self.text[i+1]
                        i += 1

                    elif self.text[i+1].isalpha():
                        raise ValueError()

                    else:
                        self.tokens.append(Token(num_str, TokenType.NUM))
                        break

            elif cur_char == '(':
                self.tokens.append(Token("(", TokenType.L_PARENTHESES))

            elif cur_char == ')':
                self.tokens.append(Token(")", TokenType.R_PARENTHESES))

            elif cur_char in ['&', '|', '=']:
                self.tokens.append(Token(cur_char, TokenType.BINARY_OP))

            elif cur_char == '!':
                if ((i + 1) < self.len_text) and (self.text[i + 1] == '='):
                    i += 1
                    self.tokens.append(Token("!=", TokenType.BINARY_OP))
                else:
                    self.tokens.append(Token("!", TokenType.UNARY_OP))

            elif cur_char == '<':
                if ((i + 1) < self.len_text) and (self.text[i + 1] == '-'):
                    i += 1
                    if ((i + 1) < self.len_text) and (self.text[i + 1] == '>'):
                        i += 1
                        self.tokens.append(Token("<->", TokenType.BINARY_OP))
                    else:
                        self.tokens.append(Token("<-", TokenType.BINARY_OP))
                else:
                    self.tokens.append(Token("<", TokenType.BINARY_OP))

            elif cur_char == '>':
                if ((i + 1) < self.len_text) and (self.text[i + 1] == '='):
                    i += 1
                    self.tokens.append(Token(">=", TokenType.BINARY_OP))
                else:
                    error_msg = "Illegal combination of chars: {0}".format(
                        self.text[i:i+2])
                    raise ValueError(error_msg)

            elif cur_char == '-':
                if ((i + 1) < self.len_text) and (self.text[i + 1] == '>'):
                    i += 1
                    self.tokens.append(Token("->", TokenType.BINARY_OP))

                elif ((i + 1) < self.len_text) and\
                        (self.text[i + 1].isdecimal()):
                    num_str = cur_char + self.text[i+1]
                    i += 1

                    if (i + 1) >= self.len_text:
                        self.tokens.append(Token(num_str, TokenType.NUM))

                    while (i + 1) < self.len_text:
                        if self.text[i + 1].isdecimal():
                            num_str += self.text[i + 1]
                            i += 1

                        elif self.text[i + 1].isalpha():
                            raise ValueError()

                        else:
                            self.tokens.append(Token(num_str, TokenType.NUM))

                else:
                    error_msg = "Illegal combination of chars: {0}".format(
                        self.text[i:i + 2])
                    raise ValueError(error_msg)

            elif cur_char == ",":
                self.tokens.append(Token(",", TokenType.ARG_DELIMITER))

            elif cur_char == "[":
                end_id = self.text.find("]", i)
                token_content = self.text[i:end_id + 1]
                self.tokens.append(Token(token_content, TokenType.NUM_ARRAY))
                i += len(token_content) - 1

            else:
                raise ValueError()

            i += 1


class Parser:
    def __init__(self, raw_text: str):

        self.tokenizer = Tokenizer(raw_text)
        self._check_formula_validity()
        self.p_map = self._get_parentheses_map()
        self.levels_map = self._get_levels_map()

    def _check_formula_validity(self):
        self._check_parentheses_balance()
        self._check_delimiter_validity()
        self._check_parentheses_validity()
        self._check_ops_inputs_validity()
        self._check_arrays_validity()

    def _check_parentheses_balance(self):
        parentheses_text = "".join([x.text for x in self.tokenizer.tokens if
                                    x.text in '()'])

        queue = []
        for p in parentheses_text:
            if p == '(':
                queue.append(')')
            else:
                if not queue or p != queue.pop():
                    raise ValueError("Parentheses aren't balanced")
        if queue:
            raise ValueError("Parentheses aren't balanced")

    def _check_parentheses_validity(self):  # checks if > 1 op or is empty
        is_already_unary_op_queue, is_already_unary_op = [], False
        is_already_binary_op_queue, is_already_binary_op = [], False
        many_ops_error_msg = "> 1 op in a single parentheses makes term vague"

        prev_token_type = None

        for token in self.tokenizer.tokens:
            cur_type = token.token_type
            if cur_type == TokenType.L_PARENTHESES:

                is_already_unary_op_queue.append(is_already_unary_op)
                is_already_binary_op_queue.append(is_already_binary_op)

                is_already_unary_op = False
                is_already_binary_op = False

            elif cur_type == TokenType.R_PARENTHESES:
                if prev_token_type == TokenType.L_PARENTHESES:
                    raise ValueError("Invalid )( adjacency found")

                is_already_unary_op = is_already_unary_op_queue.pop()
                is_already_binary_op = is_already_binary_op_queue.pop()

            elif cur_type in (TokenType.BINARY_OP, TokenType.UNARY_OP):
                if is_already_unary_op and (cur_type == TokenType.BINARY_OP):
                    raise ValueError(many_ops_error_msg)
                elif is_already_binary_op and (cur_type == TokenType.BINARY_OP):
                    raise ValueError(many_ops_error_msg)

                if cur_type == TokenType.UNARY_OP:
                    is_already_unary_op = True
                else:
                    is_already_binary_op = True

            prev_token_type = cur_type

    def _check_delimiter_validity(self):
        functions_ctxs_depth = 0
        for i, token in enumerate(self.tokenizer.tokens):
            if token.token_type == TokenType.L_PARENTHESES:
                functions_ctxs_depth += 1
            elif token.token_type == TokenType.R_PARENTHESES:
                functions_ctxs_depth -= 1
            elif token.token_type == TokenType.ARG_DELIMITER:
                if functions_ctxs_depth == 0:
                    error_msg = "Invalid delimiter location in:{0}".format(i)
                    raise ValueError(error_msg)

    def _check_ops_inputs_validity(self):
        tokens = self.tokenizer.tokens
        num_tokens = len(tokens)

        # Todo: fill value errors with appropriate messages
        for i, token in enumerate(tokens):
            if token.token_type == TokenType.UNARY_OP:
                if ((i + 1) >= num_tokens) or (tokens[i + 1].token_type not
                                               in VALID_RIGHT_INPUT_TYPES):
                    raise ValueError()
            elif token.token_type == TokenType.BINARY_OP:
                is_on_edge = (i + 1 >= num_tokens) or ((i - 1) < 0)
                if is_on_edge or (tokens[i - 1].token_type not in VALID_LEFT_INPUT_TYPES)\
                        or (tokens[i + 1].token_type not in VALID_RIGHT_INPUT_TYPES):
                    raise ValueError()

    def _check_arrays_validity(self):
        def is_number(text):
            if text.isdecimal():
                return True
            elif len(text) > 1 and text[0] == "-" and text[1:].isdecimal():
                return True
            return False

        for token in self.tokenizer.tokens:
            if token.token_type == TokenType.NUM_ARRAY:
                content_items = token.text[1:-1].split(",")

                if len(content_items) == 0:
                    raise ValueError()

                for c_item in content_items:
                    if not is_number(c_item):
                        raise ValueError()

    def _get_levels_map(self):
        levels_ops_map = defaultdict(list)
        levels_elements_map = defaultdict(list)
        cur_level = 0
        for i, token in enumerate(self.tokenizer.tokens):
            if token.token_type == TokenType.L_PARENTHESES:
                cur_level += 1
            elif token.token_type == TokenType.R_PARENTHESES:
                cur_level -= 1
            elif token.token_type in (TokenType.BINARY_OP, TokenType.UNARY_OP):
                levels_ops_map[cur_level].append(i)
            else:
                levels_elements_map[cur_level].append(i)
        keys = set(list(levels_ops_map.keys()) +
                   list(levels_elements_map.keys()))
        return {k: {"ops": levels_ops_map[k],
                    "elements": levels_elements_map[k]}
                for k in keys}

    def _get_parentheses_map(self):
        # map item structure: [id in tokens list, is_function's, partner_id]
        parentheses_map = dict()
        p_stack = []

        for i, token in enumerate(self.tokenizer.tokens):
            if token.token_type == TokenType.L_PARENTHESES:
                is_function_p = (i > 0) and\
                                self.tokenizer.tokens[i - 1].token_type ==\
                                TokenType.FUNCTION
                parentheses_map[i] = [TokenType.L_PARENTHESES, is_function_p,
                                      None]
                p_stack.append(i)
            elif token.token_type == TokenType.R_PARENTHESES:
                partner_id = p_stack[-1]
                is_function_p = parentheses_map[partner_id][1]
                parentheses_map[i] = [TokenType.R_PARENTHESES, is_function_p,
                                      partner_id]
                parentheses_map[partner_id][2] = i
                p_stack.pop()

        return parentheses_map

    def _split_function_args(self, bounds):
        args = []
        cur_arg = []
        for i in range(*bounds):
            if self.tokenizer.tokens[i].token_type != TokenType.ARG_DELIMITER:
                cur_arg.append(self.tokenizer.tokens[i])
            else:
                args.append(cur_arg)
                cur_arg = []
        if cur_arg:
            args.append(cur_arg)
        return args

    def _process_function(self, function_loc, function_level):
        function_root = self.tokenizer.tokens[function_loc]
        function_lp_loc = function_loc + 1
        function_rp_loc = self.p_map[function_lp_loc][2]
        args_bounds = (function_lp_loc + 1, function_rp_loc)
        args = self._split_function_args(args_bounds)

        args_atoms = []

        arg_lbound = args_bounds[0]
        for arg in args:
            arg_rbound = arg_lbound + len(arg) - 1
            arg_bounds = (arg_lbound, arg_rbound)
            args_atoms.append(self._helper(function_level + 1, arg_bounds))
            arg_lbound = arg_rbound + 2

        function_name = function_root.text
        inner_item = Func(function_name, args_atoms)
        return inner_item

    def _get_next_token_loc(self, level, bounds, kind):
        tokens_locs_in_level = self.levels_map.get(level, None)
        if tokens_locs_in_level:
            tokens_locs_in_level = tokens_locs_in_level.get(kind, None)
            for token_loc in tokens_locs_in_level:
                if (token_loc >= bounds[0]) and (token_loc <= bounds[1]):
                    return token_loc
        return None

    def _process_right_item(self, loc, level, parent_bounds):
        next_token = self.tokenizer.tokens[loc]

        if next_token.token_type == TokenType.VAR:
            inner_item = Var(next_token.text)

        elif next_token.token_type == TokenType.FUNCTION:
            inner_item = self._process_function(loc, level)

        elif next_token.token_type == TokenType.L_PARENTHESES:
            new_bounds = (loc, self.p_map[loc][2])
            inner_item = self._helper(level + 1, new_bounds)

        elif next_token.token_type == TokenType.UNARY_OP:
            new_bounds = (loc + 1, parent_bounds[1])
            inner_inner_item = self._helper(level, new_bounds)
            inner_item = BLOCKS_MAP[next_token.text](inner_inner_item)

        else:
            raise ValueError()
        return inner_item

    def _process_left_item(self, loc, level):
        prev_token = self.tokenizer.tokens[loc]

        if prev_token.token_type == TokenType.VAR:
            left_item = Var(prev_token.text)

        elif prev_token.token_type == TokenType.R_PARENTHESES:
            if self.p_map[loc][1]:
                # function processing
                function_root_loc = self.p_map[loc][2] - 1
                left_item = self._process_function(function_root_loc, level)
            else:
                # process regular ()
                new_bounds = (self.p_map[loc][2], loc)
                left_item = self._helper(level + 1, new_bounds)

        else:
            raise ValueError("Invalid left item: {0}".format(prev_token.text))

        return left_item

    def _process_op(self, op_loc, op_level, cur_bounds):
        op_token = self.tokenizer.tokens[op_loc]
        if op_token.token_type == TokenType.UNARY_OP:
            inner_item = self._process_right_item(op_loc + 1, op_level,
                                                  cur_bounds)
            return BLOCKS_MAP[op_token.text](inner_item)

        elif op_token.text in INEQUALITIES_OPS_TEXTS:
            if (op_loc <= 0) or (op_loc >= len(self.tokenizer.tokens) - 1):
                raise ValueError()

            prev_token = self.tokenizer.tokens[op_loc - 1]
            next_token = self.tokenizer.tokens[op_loc + 1]
            if prev_token.token_type != TokenType.NUM_ARRAY or\
                    next_token.token_type != TokenType.NUM:
                raise ValueError()
            left_item = np.array([int(x) for x in
                                  prev_token.text[1:-1].split(",")])
            right_item = int(next_token.text)
            return BLOCKS_MAP[op_token.text](left_item, right_item)

        else:  # Binary op which isn't an inequality
            right_item = self._process_right_item(op_loc + 1, op_level,
                                                  cur_bounds)
            left_item = self._process_left_item(op_loc - 1, op_level)

            if op_token.text == "<-":
                left_item, right_item = right_item, left_item

            return BLOCKS_MAP[op_token.text](left_item, right_item)

    def _helper(self, cur_level, bounds):
        chosen_op_loc = self._get_next_token_loc(cur_level, bounds, kind="ops")

        if chosen_op_loc is not None:
            return self._process_op(chosen_op_loc, cur_level, bounds)

        else:  # process non-op
            token_loc = self._get_next_token_loc(cur_level, bounds,
                                                 kind="elements")
            if token_loc is not None:
                cur_token = self.tokenizer.tokens[token_loc]
                if cur_token.token_type == TokenType.FUNCTION:
                    return self._process_function(token_loc, cur_level)
                else:
                    return Var(cur_token.text)
            else:
                return self._helper(cur_level + 1, bounds)

    def parse(self):
        cur_level = 0
        bounds = (0, len(self.tokenizer.tokens) - 1)

        return self._helper(cur_level, bounds)
