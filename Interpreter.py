from ast import keyword
import inspect
import operator
import sys
import types
import dis
import collections

Block = collections.namedtuple("Block", ["type", "handler", "stack_height"])


class VirtualMachineError(Exception):
    pass


class VirtualMachine:
    def __init__(self):
        self.call_stack = []
        self.data_stack = []
        self.frame = None  # The current frame
        self.return_value = None
        self.last_exception = None

    def run_code(self, code, global_names=None, local_names=None):
        frame = self.make_frame(
            code, global_names=global_names, local_names=local_names
        )
        self.run_frame(frame)

    def make_frame(self, code, callargs={}, global_names=None, local_names=None):
        if global_names is not None and local_names is not None:
            local_names = global_names
        elif self.call_stack:
            global_names = self.frame.global_names
            local_names = {}
        else:
            global_names = local_names = {
                "__builtins__": __builtins__,
                "__name__": "__main__",
                "__doc__": None,
                "__package__": None,
            }
        local_names.update(callargs)
        frame = Frame(code, global_names, local_names, self.frame)
        return frame

    def push_frame(self, frame):
        self.call_stack.append(frame)
        self.frame = frame

    def pop_frame(self):
        self.call_stack.pop()
        if self.call_stack:
            self.frame = self.call_stack[-1]
        else:
            self.frame = None

    def run_frame(self, frame):
        self.push_frame(frame)
        while True:
            byte_name, argument = self.parse_byte_and_args()
            why = self.dispatch(byte_name, argument)
            while why and frame.block_stack:
                why = self.manage_block_stack(why)
            if why:
                break
        self.pop_frame()
        if why == "exception":
            exc, val, tb = self.last_exception
            e = exc(val)
            e.__traceback__ = tb
            raise e
        return self.return_value

    def top(self):
        return self.data_stack[-1]

    def pop(self):
        return self.data_stack.pop()

    def push(self, *vals):
        self.data_stack.extend(vals)

    def peek(self, n):
        return self.data_stack[-n]

    def popn(self, n):

        if n:
            ret = self.data_stack[-n:]
            self.data_stack[-n:] = []
            return ret
        else:
            return []

    def parse_byte_and_args(self):
        f = self.frame
        opoffset = f.last_instruction
        byte_code = f.code_obj.co_code[opoffset]
        byte_name = dis.opname[byte_code]
        f.last_instruction += 1
        if byte_code >= dis.HAVE_ARGUMENT:
            arg = f.code_obj.co_code[f.last_instruction]
            f.last_instruction += 1

            if byte_code in dis.hasconst:
                arg = f.code_obj.co_consts[arg]
            elif byte_code in dis.hasname:
                arg = f.code_obj.co_names[arg]
            elif byte_code in dis.haslocal:
                arg = f.code_obj.co_varnames[arg]
            elif byte_code in dis.hasjrel:
                arg = f.last_instruction + arg * 2
            elif byte_code in dis.hasjabs:
                arg *= 2
            argument = [arg]
        else:
            argument = []
            f.last_instruction += 1
        return byte_name, argument

    def dispatch(self, byte_name, argument):

        why = None
        try:
            bytecode_fn = getattr(self, f"byte_{byte_name}", None)
            if bytecode_fn is None:
                if byte_name.startswith("UNARY_"):
                    bytecode_fn = getattr(self, f"byte_UNARY_{byte_name[6:]}")
                elif byte_name.startswith("BINARY_"):
                    bytecode_fn = getattr(self, f"byte_BINARY_{byte_name[7:]}")
                elif byte_name.startswith("INPLACE_"):
                    bytecode_fn = getattr(self, f"byte_INPLACE_{byte_name[8:]}")

                else:
                    raise VirtualMachineError(f"unsupported bytecode {byte_name}")

            why = bytecode_fn(*argument)
        except:
            self.last_exception = sys.exc_info()[:2] + (None,)
            why = "exception"

        return why

    def push_block(self, b_type, handler=None):
        stack_height = len(self.data_stack)
        self.frame.block_stack.append(Block(b_type, handler, stack_height))

    def pop_block(self):
        return self.frame.block_stack.pop()

    def unwind_block(self, block):
        if block.type == "except-handler":
            offset = 3
        else:
            offset = 0

        while len(self.frame.stack) > block.level + offset:
            self.pop()

        if block.type == "except-handler":
            tb, value, exctype = self.popn(3)
            self.last_exception = exctype, value, tb

    def manage_block_stack(self, why):
        """Manage a frame's block stack.
        Manipulate the block stack,
        exception handling, or returning."""
        assert why != "yield"

        block = self.frame.block_stack[-1]
        if block.type == "loop" and why == "continue":
            self.jump(self.return_value)
            why = None
            return why

        self.pop_block()
        self.unwind_block(block)

        if block.type == "loop" and why == "break":
            why = None
            self.jump(block.handler)
            return why

        if why == "exception" and block.type in ["setup-except", "finally"]:
            self.push_block("except-handler")
            exctype, value, tb = self.last_exception
            self.push(tb, value, exctype)
            self.push(tb, value, exctype)
            why = None
            self.jump(block.handler)
            return why

        elif block.type == "finally":
            if why in ("return", "continue"):
                self.push(self.return_value)
            self.push(why)

            why = None
            self.jump(block.handler)
            return why

        return why

    def byte_LOAD_CONST(self, const):
        self.push(const)

    def byte_POP_TOP(self):
        self.pop()

    def byte_DUP_TOP(self):
        self.push(self.top())

    def byte_DUP_TOPX(self, count):
        items = self.popn(count)
        for i in [1, 2]:
            self.push(*items)

    def byte_DUP_TOP_TWO(self):
        a, b = self.popn(2)
        self.push(a, b, a, b)

    def byte_ROT_TWO(self):
        a, b = self.popn(2)
        self.push(b, a)

    def byte_ROT_THREE(self):
        a, b, c = self.popn(3)
        self.push(c, a, b)

    def byte_ROT_FOUR(self):
        a, b, c, d = self.popn(4)
        self.push(d, a, b, c)

    ## Names

    def byte_LOAD_NAME(self, name):
        frame = self.frame
        if name in frame.local_names:
            val = frame.local_names[name]
        elif name in frame.global_names:
            val = frame.global_names[name]
        elif name in frame.builtin_names:
            val = frame.builtin_names[name]
        else:
            raise NameError(f"name '{name}' is not defined")
        self.push(val)

    def byte_STORE_NAME(self, name):
        self.frame.local_names[name] = self.pop()

    def byte_DELETE_NAME(self, name):
        del self.frame.local_names[name]

    def byte_LOAD_FAST(self, name):
        if name in self.frame.local_names:
            val = self.frame.local_names[name]
        else:
            raise UnboundLocalError(
                f"local variable '{name}' referenced before assignment"
            )
        self.push(val)

    def byte_STORE_FAST(self, name):
        self.frame.local_names[name] = self.pop()

    def byte_DELETE_FAST(self, name):
        del self.frame.local_names[name]

    def byte_LOAD_GLOBAL(self, name):
        f = self.frame
        if name in f.global_names:
            val = f.global_names[name]
        elif name in f.builtin_names:
            val = f.builtin_names[name]
        else:
            raise NameError(f"global name '{name}' is not defined")
        self.push(val)

    def byte_STORE_GLOBAL(self, name):
        f = self.frame
        f.global_names[name] = self.pop()

    def byte_LOAD_LOCALS(self):
        self.push(self.frame.local_names)

    ## Operators

    UNARY_OPERATORS = {
        "POSITIVE": operator.pos,
        "NEGATIVE": operator.neg,
        "NOT": operator.not_,
        "CONVERT": repr,
        "INVERT": operator.invert,
    }

    def unaryOperator(self, op):
        x = self.pop()
        self.push(self.UNARY_OPERATORS[op](x))

    def byte_UNARY_POSITIVE(self):
        self.unaryOperator("POSITIVE")

    def byte_UNARY_NEGATIVE(self):
        self.unaryOperator("NEGATIVE")

    def byte_UNARY_NOT(self):
        self.unaryOperator("NOT")

    def byte_UNARY_CONVERT(self):
        self.unaryOperator("CONVERT")

    def byte_UNARY_INVERT(self):
        self.unaryOperator("INVERT")

    BINARY_OPERATORS = {
        "POWER": pow,
        "MULTIPLY": operator.mul,
        "DIVIDE": getattr(operator, "div", lambda x, y: None),
        "FLOOR_DIVIDE": operator.floordiv,
        "TRUE_DIVIDE": operator.truediv,
        "MODULO": operator.mod,
        "ADD": operator.add,
        "SUBTRACT": operator.sub,
        "SUBSCR": operator.getitem,
        "LSHIFT": operator.lshift,
        "RSHIFT": operator.rshift,
        "AND": operator.and_,
        "XOR": operator.xor,
        "OR": operator.or_,
    }

    def binaryOperator(self, op):
        x, y = self.popn(2)
        self.push(self.BINARY_OPERATORS[op](x, y))

    def byte_BINARY_POWER(self):
        self.binaryOperator("POWER")

    def byte_BINARY_MULTIPLY(self):
        self.binaryOperator("MULTIPLY")

    def byte_BINARY_DIVIDE(self):
        self.binaryOperator("DIVIDE")

    def byte_BINARY_FLOOR_DIVIDE(self):
        self.binaryOperator("FLOOR_DIVIDE")

    def byte_BINARY_TRUE_DIVIDE(self):
        self.binaryOperator("TRUE_DIVIDE")

    def byte_BINARY_MODULO(self):
        self.binaryOperator("MODULO")

    def byte_BINARY_ADD(self):
        self.binaryOperator("ADD")

    def byte_BINARY_SUBTRACT(self):
        self.binaryOperator("SUBTRACT")

    def byte_BINARY_SUBSCR(self):
        self.binaryOperator("SUBSCR")

    def byte_BINARY_LSHIFT(self):
        self.binaryOperator("LSHIFT")

    def byte_BINARY_RSHIFT(self):
        self.binaryOperator("RSHIFT")

    def byte_BINARY_AND(self):
        self.binaryOperator("AND")

    def byte_BINARY_OR(self):
        self.binaryOperator("OR")

    def byte_BINARY_XOR(self):
        self.binaryOperator("XOR")

    def inplaceOperator(self, op):
        x, y = self.popn(2)
        if op == "POWER":
            x **= y
        elif op == "MULTIPLY":
            x *= y
        elif op in ["DIVIDE", "FLOOR_DIVIDE"]:
            x //= y
        elif op == "TRUE_DIVIDE":
            x /= y
        elif op == "MODULO":
            x %= y
        elif op == "ADD":
            x += y
        elif op == "SUBTRACT":
            x -= y
        elif op == "LSHIFT":
            x <<= y
        elif op == "RSHIFT":
            x >>= y
        elif op == "AND":
            x &= y
        elif op == "XOR":
            x ^= y
        elif op == "OR":
            x |= y
        else:
            raise VirtualMachineError(f"Unknown in-place operator: {op}")
        self.push(x)

    def byte_INPLACE_POWER(self):
        self.inplaceOperator("POWER")

    def byte_INPLACE_MULTIPLY(self):
        self.inplaceOperator("MULTIPLY")

    def byte_INPLACE_DIVIDE(self):
        self.inplaceOperator("DIVIDE")

    def byte_INPLACE_FLOOR_DIVIDE(self):
        self.inplaceOperator("FLOOR_DIVIDE")

    def byte_INPLACE_TRUE_DIVIDE(self):
        self.inplaceOperator("TRUE_DIVIDE")

    def byte_INPLACE_MODULO(self):
        self.inplaceOperator("MODULO")

    def byte_INPLACE_ADD(self):
        self.inplaceOperator("ADD")

    def byte_INPLACE_SUBTRACT(self):
        self.inplaceOperator("SUBTRACT")

    def byte_INPLACE_LSHIFT(self):
        self.inplaceOperator("LSHIFT")

    def byte_INPLACE_RSHIFT(self):
        self.inplaceOperator("RSHIFT")

    def byte_INPLACE_AND(self):
        self.inplaceOperator("AND")

    def byte_INPLACE_XOR(self):
        self.inplaceOperator("XOR")

    def byte_INPLACE_OR(self):
        self.inplaceOperator("OR")

    def sliceOperator(self, op):
        start = 0
        end = None
        op, count = op[:-2], int(op[-1])
        if count == 1:
            start = self.pop()
        elif count == 2:
            end = self.pop()
        elif count == 3:
            end = self.pop()
            start = self.pop()
        l = self.pop()
        if end is None:
            end = len(l)
        if op.startswith("STORE_"):
            l[start:end] = self.pop()
        elif op.startswith("DELETE_"):
            del l[start:end]
        else:
            self.push(l[start:end])

    COMPARE_OPERATORS = [
        operator.lt,
        operator.le,
        operator.eq,
        operator.ne,
        operator.gt,
        operator.ge,
        lambda x, y: x in y,
        lambda x, y: x not in y,
        lambda x, y: x is y,
        lambda x, y: x is not y,
        lambda x, y: issubclass(x, Exception) and issubclass(x, y),
    ]

    def byte_COMPARE_OP(self, operator_number):
        x, y = self.popn(2)
        self.push(self.COMPARE_OPERATORS[operator_number](x, y))

    ## Attributes and indexing

    def byte_LOAD_ATTR(self, attr):
        obj = self.pop()
        val = getattr(obj, attr)
        self.push(val)

    def byte_STORE_ATTR(self, name):
        val, obj = self.popn(2)
        setattr(obj, name, val)

    def byte_DELETE_ATTR(self, name):
        obj = self.pop()
        delattr(obj, name)

    def byte_STORE_SUBSCR(self):
        val, obj, subscr = self.popn(3)
        obj[subscr] = val

    def byte_DELETE_SUBSCR(self):
        obj, subscr = self.popn(2)
        del obj[subscr]

    ## Building

    def byte_BUILD_TUPLE(self, count):
        elements = self.popn(count)
        self.push(tuple(elements))

    def byte_BUILD_LIST(self, count):
        elements = self.popn(count)
        self.push(elements)

    def byte_BUILD_SET(self, count):
        elements = self.popn(count)
        self.push(set(elements))

    def byte_BUILD_MAP(self, size):
        items = self.popn(2 * size)
        keys = items[0::2]
        values = items[1::2]
        self.push(dict(zip(keys, values)))

    def byte_UNPACK_SEQUENCE(self, count):
        seq = self.pop()
        for x in reversed(seq):
            self.push(x)

    def byte_BUILD_SLICE(self, count):
        if count == 2:
            x, y = self.popn(2)
            self.push(slice(x, y))
        elif count == 3:
            x, y, z = self.popn(3)
            self.push(slice(x, y, z))
        else:
            raise VirtualMachineError(f"Strange BUILD_SLICE count: {count}")

    def byte_LIST_APPEND(self, count):
        val = self.pop()
        the_list = self.peek(count)
        the_list.append(val)

    def byte_SET_ADD(self, count):
        val = self.pop()
        the_set = self.peek(count)
        the_set.add(val)

    def byte_MAP_ADD(self, count):
        key, val = self.popn(2)
        print(key, val)
        the_map = self.peek(count)
        the_map[key] = val

    ## Jumps

    def jump(self, jump):
        self.frame.last_instruction = jump

    def byte_JUMP_FORWARD(self, jump):
        self.jump(jump)

    def byte_JUMP_ABSOLUTE(self, jump):
        self.jump(jump)

    def byte_POP_JUMP_IF_TRUE(self, jump):
        val = self.pop()
        if val:
            self.jump(jump)

    def byte_POP_JUMP_IF_FALSE(self, jump):
        val = self.pop()
        if not val:
            self.jump(jump)

    def byte_JUMP_IF_TRUE_OR_POP(self, jump):
        val = self.top()
        if val:
            self.jump(jump)
        else:
            self.pop()

    def byte_JUMP_IF_FALSE_OR_POP(self, jump):
        val = self.top()
        if not val:
            self.jump(jump)
        else:
            self.pop()

    ## Blocks

    def byte_SETUP_LOOP(self, dest):
        self.push_block("loop", dest)

    def byte_GET_ITER(self):
        self.push(iter(self.pop()))

    def byte_FOR_ITER(self, jump):
        iterator_object = self.top()
        try:
            v = next(iterator_object)
            self.push(v)
        except StopIteration:
            self.pop()
            self.jump(jump)

    def byte_SETUP_FINALLY(self, dest):
        self.push_block("finally", dest)

    def byte_POP_BLOCK(self):
        self.pop_block()

    def byte_POP_EXCEPT(self):
        block = self.pop_block()
        if block.type != "except-handler":
            raise Exception("popped block is not an except handler")
        self.unwind_block(block)

    def byte_SETUP_WITH(self, dest):
        context_manager = self.pop()
        self.push(context_manager.__exit__)
        context_manager_obj = context_manager.__enter__()
        self.push_block("finally", dest)
        self.push(context_manager_obj)

    ## Functions

    def byte_MAKE_FUNCTION(self, argc):

        name = self.pop()
        code = self.pop()
        defaults = self.popn(argc)
        globs = self.frame.global_names
        fn = Function(name, code, globs, defaults, self)
        self.push(fn)

    def byte_CALL_FUNCTION(self, arg):
        return self.call_function(arg, [], {})

    def byte_CALL_FUNCTION_VAR(self, arg):
        args = self.pop()
        return self.call_function(arg, args, {})

    def byte_CALL_FUNCTION_KW(self, arg):
        kwargs = self.pop()
        return self.call_function(arg, [], kwargs)

    def byte_CALL_FUNCTION_VAR_KW(self, arg):
        args, kwargs = self.popn(2)
        return self.call_function(arg, args, kwargs)

    def call_function(self, arg, args, kwargs):
        keyword_argument_length, positional_arguments_length = divmod(arg, 256)
        named_args = {}
        for _ in range(keyword_argument_length):
            key, val = self.popn(2)
            named_args[key] = val
        named_args.update(kwargs)
        positional_arguments = self.popn(positional_arguments_length)
        positional_arguments.extend(args)

        func = self.pop()
        if hasattr(func, "im_func"):
            if func.im_self:
                positional_arguments.insert(0, func.im_self)
            if not isinstance(positional_arguments[0], func.im_class):
                raise TypeError(
                    f"unbound method {func.im_func.func_name}() must be called with {func.im_class.__name__} instance "
                    f"as first argument (got {type(positional_arguments[0]).__name__} instance instead)"
                )
            func = func.im_func
        retval = func(*positional_arguments, **named_args)
        self.push(retval)

    def byte_RETURN_VALUE(self):
        self.return_value = self.pop()
        return "return"


class Frame:
    def __init__(self, code_obj, global_names, local_names, prev_frame):
        self.code_obj = code_obj
        self.global_names = global_names
        self.local_names = local_names
        self.prev_frame = prev_frame
        if prev_frame:
            self.builtin_names = prev_frame.builtin_names
        else:
            self.builtin_names = local_names["__builtins__"]
            if hasattr(self.builtin_names, "__dict__"):
                self.builtin_names = self.builtin_names.__dict__

        self.last_instruction = 0
        self.block_stack = []


class Function:
    __slots__ = [
        "func_code",
        "func_name",
        "func_defaults",
        "func_globals",
        "func_locals",
        "func_dict",
        "__name__",
        "__dict__",
        "_vm",
        "_func",
    ]

    def __init__(self, name, code, globs, defaults, vm):
        self._vm = vm
        self.func_code = code
        self.func_name = self.__name__ = name or code.co_name
        self.func_defaults = tuple(defaults)
        self.func_globals = globs
        self.func_locals = self._vm.frame.local_names
        self.__dict__ = {}

        kw = {
            "argdefs": self.func_defaults,
        }
        self._func = types.FunctionType(code, globs, **kw)

    def __call__(self, *args, **kwargs):
        callargs = inspect.getcallargs(self._func, *args, **kwargs)

        frame = self._vm.make_frame(self.func_code, callargs, self.func_globals, {})
        return self._vm.run_frame(frame)


def run_interpreter_on_file(path, interpreter):
    open_file = open(path)
    source_code = open_file.read()
    open_file.close()
    byte_code = compile(source_code, path, "exec")
    interpreter.run_code(byte_code)


def run_interpreter_on_string(string, intperperter):
    byte_code = compile(string, "", "exec")
    intperperter.run_code(byte_code)


"""********************  put the path to your file in the 'path' variable  ********************"""
Path = "Put your file path here"
interpreter = VirtualMachine()
run_interpreter_on_file(Path, interpreter)
