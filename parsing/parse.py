from dataclasses import dataclass
from enum import Enum
from collections import defaultdict, deque
from parsing.logical_blocks import *


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
                          TokenType.R_PARENTHESES, TokenType.NUM_ARRAY,
                          TokenType.NUM]
VALID_RIGHT_INPUT_TYPES = [TokenType.VAR, TokenType.FUNCTION,
                           TokenType.L_PARENTHESES, TokenType.UNARY_OP,
                           TokenType.NUM_ARRAY, TokenType.NUM]


@dataclass
class Token:
    text: str
    token_type: TokenType


class Tokenizer:
    def __init__(self):
        self.tokens = []
        self.text, self.len_text = "", 0
        self.cur_i = 0

    def reset(self):
        self.tokens = []
        self.text = ""
        self.len_text = 0
        self.cur_i = 0

    def _process_var_or_function(self):
        atom_name = self.text[self.cur_i]
        if (self.cur_i + 1) >= self.len_text:
            self.tokens.append(Token(atom_name, TokenType.VAR))

        while (self.cur_i + 1) < self.len_text:
            if self.text[self.cur_i + 1].isalnum():
                atom_name += self.text[self.cur_i + 1]
                self.cur_i += 1

                if (self.cur_i + 1) >= self.len_text:
                    self.tokens.append(Token(atom_name, TokenType.VAR))

            elif self.text[self.cur_i + 1] == "(":
                self.tokens.append(Token(atom_name, TokenType.FUNCTION))
                break

            else:
                self.tokens.append(Token(atom_name, TokenType.VAR))
                break

    def _process_num(self):
        num_str = self.text[self.cur_i]
        if (self.cur_i + 1) >= self.len_text:
            self.tokens.append(Token(num_str, TokenType.NUM))

        else:
            while (self.cur_i + 1) < self.len_text:
                if self.text[self.cur_i + 1].isdecimal():
                    num_str += self.text[self.cur_i + 1]
                    self.cur_i += 1

                elif self.text[self.cur_i + 1].isalpha():
                    error_msg = f"Invalid num followed by a letter:" \
                                f" {num_str + self.text[self.cur_i]} "
                    raise ValueError(error_msg)

                else:
                    break
            self.tokens.append(Token(num_str, TokenType.NUM))

    def _process_negations_or_neqs(self):
        if ((self.cur_i + 1) < self.len_text) and\
                (self.text[self.cur_i + 1] == '='):
            self.cur_i += 1
            self.tokens.append(Token("!=", TokenType.BINARY_OP))
        else:
            self.tokens.append(Token("!", TokenType.UNARY_OP))

    def _process_right_imply_negatives(self):
        if ((self.cur_i + 1) < self.len_text) and \
                (self.text[self.cur_i + 1] == '>'):
            self.cur_i += 1
            self.tokens.append(Token("->", TokenType.BINARY_OP))

        elif ((self.cur_i + 1) < self.len_text) and \
                (self.text[self.cur_i + 1].isdecimal()):
            num_str = self.text[self.cur_i] + self.text[self.cur_i + 1]
            self.cur_i += 1

            if (self.cur_i + 1) >= self.len_text:
                self.tokens.append(Token(num_str, TokenType.NUM))

            while (self.cur_i + 1) < self.len_text:
                if self.text[self.cur_i + 1].isdecimal():
                    num_str += self.text[self.cur_i + 1]
                    self.cur_i += 1

                elif self.text[self.cur_i + 1].isalpha():
                    error_msg = f"Invalid num followed by a letter:" \
                                f" {num_str + self.text[self.cur_i]} "
                    raise ValueError(error_msg)

                else:
                    self.tokens.append(Token(num_str, TokenType.NUM))
                    break
        else:
            error_msg = f"Illegal combination of chars: " \
                        f"{self.text[self.cur_i:self.cur_i + 2]}"
            raise ValueError(error_msg)

    def _process_less_equiv_left_imply(self):
        if ((self.cur_i + 1) < self.len_text) and \
                (self.text[self.cur_i + 1] == '-'):
            self.cur_i += 1

            if ((self.cur_i + 1) < self.len_text) and \
                    (self.text[self.cur_i + 1].isdecimal()):
                self.tokens.append(Token("<", TokenType.BINARY_OP))

            elif ((self.cur_i + 1) < self.len_text) and \
                    (self.text[self.cur_i + 1] == '>'):
                self.cur_i += 1
                self.tokens.append(Token("<->", TokenType.BINARY_OP))

            else:
                self.tokens.append(Token("<-", TokenType.BINARY_OP))

        else:
            self.tokens.append(Token("<", TokenType.BINARY_OP))

    def _process_geqs(self):
        if ((self.cur_i + 1) < self.len_text) and \
                (self.text[self.cur_i + 1] == '='):
            self.cur_i += 1
            self.tokens.append(Token(">=", TokenType.BINARY_OP))

        else:
            error_msg = f"Illegal combination of chars: " \
                        f"{self.text[self.cur_i:self.cur_i + 2]}"

            raise ValueError(error_msg)

    def _process_num_array(self):
        end_id = self.text.find("]", self.cur_i)
        token_content = self.text[self.cur_i:end_id + 1]
        self.tokens.append(Token(token_content, TokenType.NUM_ARRAY))
        self.cur_i += len(token_content) - 1

    def tokenize(self, raw_text: str):
        self.reset()
        self.text = raw_text.replace(" ", "")
        self.len_text = len(self.text)

        while self.cur_i < self.len_text:
            cur_char = self.text[self.cur_i]

            if cur_char.isalpha():
                self._process_var_or_function()

            elif cur_char.isdecimal():
                self._process_num()

            elif cur_char == '(':
                self.tokens.append(Token("(", TokenType.L_PARENTHESES))

            elif cur_char == ')':
                self.tokens.append(Token(")", TokenType.R_PARENTHESES))

            elif cur_char in ['&', '|', '=']:
                self.tokens.append(Token(cur_char, TokenType.BINARY_OP))

            elif cur_char == '!':
                self._process_negations_or_neqs()

            elif cur_char == '<':
                self._process_less_equiv_left_imply()

            elif cur_char == '>':
                self._process_geqs()

            elif cur_char == '-':
                self._process_right_imply_negatives()

            elif cur_char == ",":
                self.tokens.append(Token(",", TokenType.ARG_DELIMITER))

            elif cur_char == "[":
                self._process_num_array()

            else:
                raise ValueError(f"Unable to parse {cur_char} to token")

            self.cur_i += 1


class Parser:
    def __init__(self):

        self.tokenizer = Tokenizer()
        self.p_map = dict()
        self.levels_map = dict()

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

            elif cur_type == TokenType.ARG_DELIMITER:
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
        cur_inner_function_level = 0
        inner_functions_levels = deque()
        for i, token in enumerate(self.tokenizer.tokens):
            if token.token_type == TokenType.FUNCTION:
                inner_functions_levels.append(cur_inner_function_level)
                functions_ctxs_depth += 1
                cur_inner_function_level = 0

            elif token.token_type == TokenType.L_PARENTHESES and\
                    functions_ctxs_depth > 0:
                cur_inner_function_level += 1

            elif token.token_type == TokenType.R_PARENTHESES and \
                    functions_ctxs_depth > 0:
                cur_inner_function_level -= 1
                if cur_inner_function_level == 0:
                    functions_ctxs_depth -= 1
                    cur_inner_function_level = inner_functions_levels.pop()

            elif token.token_type == TokenType.ARG_DELIMITER:
                if functions_ctxs_depth == 0:
                    error_msg = f"Invalid delimiter location in: {i}"
                    raise ValueError(error_msg)

    def _check_ops_inputs_validity(self):
        tokens = self.tokenizer.tokens
        num_tokens = len(tokens)

        for i, token in enumerate(tokens):
            if token.token_type == TokenType.UNARY_OP:
                if (i + 1) >= num_tokens:
                    error_msg = f"Unary Operation {token.text} at the end" \
                                f" of formula text with no item to act on"
                    raise ValueError(error_msg)

                elif tokens[i + 1].token_type not in VALID_RIGHT_INPUT_TYPES:
                    error_msg = f"Invalid argument to unary" \
                                f" operation {token.text}"
                    raise ValueError(error_msg)

            elif token.token_type == TokenType.BINARY_OP:
                is_on_edge = (i + 1 >= num_tokens) or ((i - 1) < 0)
                if is_on_edge:
                    error_msg = f"Binary Operation {token.text} don't have" \
                                f" an argument to his left or right "
                    raise ValueError(error_msg)

                elif tokens[i - 1].token_type not in VALID_LEFT_INPUT_TYPES:
                    error_msg = f"Invalid left argument to binary" \
                                f" operation {token.text}"
                    raise ValueError(error_msg)

                elif tokens[i + 1].token_type not in VALID_RIGHT_INPUT_TYPES:
                    error_msg = f"Invalid right argument to binary" \
                                f" operation {token.text}"
                    raise ValueError(error_msg)

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
                    raise ValueError("Encountered an empty array")

                for c_item in content_items:
                    if not is_number(c_item):
                        error_msg = f"{c_item} isn't a number in" \
                                    f" array [{content_items}]"
                        raise ValueError(error_msg)

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
        args, cur_arg = [], []
        i = bounds[0]
        while i < bounds[1]:
            cur_token = self.tokenizer.tokens[i]

            if cur_token.token_type == TokenType.FUNCTION:
                right_parenthesis_id = self.p_map[i+1][2]
                func_tokens = self.tokenizer.tokens[i: right_parenthesis_id + 1]
                cur_arg.extend(func_tokens)
                i += right_parenthesis_id - i

            elif cur_token.token_type == TokenType.ARG_DELIMITER:
                args.append(cur_arg)
                cur_arg = []

            else:
                cur_arg.append(self.tokenizer.tokens[i])
            i += 1

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
            right_item = Var(next_token.text)

        elif next_token.token_type == TokenType.FUNCTION:
            right_item = self._process_function(loc, level)

        elif next_token.token_type == TokenType.L_PARENTHESES:
            new_bounds = (loc + 1, self.p_map[loc][2])
            right_item = self._helper(level + 1, new_bounds)

        elif next_token.token_type == TokenType.UNARY_OP:
            new_bounds = (loc + 1, parent_bounds[1])
            inner_inner_item = self._helper(level, new_bounds)
            right_item = BLOCKS_MAP[next_token.text](inner_inner_item)

        elif next_token.token_type == TokenType.NUM_ARRAY:
            right_item = np.array([int(x) for x in
                                  next_token.text[1:-1].split(",")])

        elif next_token.token_type == TokenType.NUM:
            right_item = int(next_token.text)

        else:
            error_msg = f"Unexpected token {next_token.text} of type " \
                        f"{next_token.token_type} to serve as a right argument"
            raise ValueError(error_msg)

        return right_item

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
                new_bounds = (self.p_map[loc][2] + 1, loc)
                left_item = self._helper(level + 1, new_bounds)

        elif prev_token.token_type == TokenType.NUM_ARRAY:
            left_item = np.array([int(x) for x in
                                  prev_token.text[1:-1].split(",")])

        elif prev_token.token_type == TokenType.NUM:
            left_item = int(prev_token.text)

        else:
            raise ValueError(f"Invalid left item: {prev_token.text}")

        return left_item

    def _process_op(self, op_loc, op_level, cur_bounds):
        op_token = self.tokenizer.tokens[op_loc]
        if op_token.token_type == TokenType.UNARY_OP:
            inner_item = self._process_right_item(op_loc + 1, op_level,
                                                  cur_bounds)
            return BLOCKS_MAP[op_token.text](inner_item)

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

    def parse(self, raw_text: str):
        self.tokenizer.tokenize(raw_text)

        self._check_formula_validity()
        self.p_map = self._get_parentheses_map()
        self.levels_map = self._get_levels_map()

        if not self.tokenizer.tokens:
            return None

        cur_level = 0
        bounds = (0, len(self.tokenizer.tokens) - 1)

        return self._helper(cur_level, bounds)
