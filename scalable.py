import inspect
import itertools
from pyeda.inter import *
import struct
import numpy as np
from pysat.formula import IDPool
from pysat.card import CardEnc
from pysat.solvers import Solver

def fmt_bytes(fmt):
    res = 0
    i = 0
    while i < len(fmt):
        length = 0
        while fmt[i].isnumeric():
            length = 10*length + int(fmt[i])
            i += 1
        if length == 0:
            length = 1
        if fmt[i] in ("[", "]"):
            i += 1
            continue
        if fmt[i] in ('f', 'i'):
            res += 32 * length
            i += 1
            continue
        if fmt[i] in ('s'):
            res += 8 * length
            i += 1
            continue
        raise SyntaxError("Unrecognized format symbol")
    return res

def bit_unpack(b):
    return [(byte >> i) & 1 for byte in b for i in range(8)]

def unpack(value, length):
    if isinstance(value, int):
        return bit_unpack(struct.pack('i', value))
    if isinstance(value, float):
        return bit_unpack(struct.pack('f', value))
    if isinstance(value, str):
        return bit_unpack(struct.pack(f'{length}s', value.encode()))

def unpacks(argset, fmt):
    if not isinstance(argset, tuple):
        argset = (argset,)
    objects = 0
    depth = 0
    for i in range(len(fmt)):
        if fmt[i] in ('i', 'f', 's') and depth == 0:
            objects += 1
        elif fmt[i] == '[':
            if depth == 0:
                objects += 1
            depth += 1
        elif fmt[i] == ']':
            if depth <= 0:
                raise SyntaxError("Format dangling bracket")
            depth -= 1
    if depth != 0:
        raise SyntaxError("Format unpaired bracket")
    if isinstance(argset, (tuple)):
        if objects != len(argset):
            raise SyntaxError("Format length mismatch")
    binary = []
    i = 0
    obj = 0
    while i < len(fmt):
        length = 0
        while fmt[i].isnumeric():
            length = 10*length + int(fmt[i])
            i += 1
        if length == 0:
            length = 1
        if fmt[i] == "[":
            c = 0
            j = i + 1
            while j < len(fmt):
                if fmt[j] == "[":
                    c += 1
                elif fmt[j] == "]" and c == 0:
                    binary.extend(unpacks(argset[obj], fmt[i+1:j-1]))
                    i = j + 1
                    break
                elif fmt[j] == "]":
                    c -= 1
        elif fmt[i] in ('i', 'f', 's'):
            binary.extend(unpack(argset[obj], length))
        obj += 1
        i += 1
    return tuple(binary)

class BitReader:
    def __init__(self, bits):
        self.bits = bits
        self.pos = 0

    def take(self, n):
        chunk = self.bits[self.pos:self.pos+n]
        if len(chunk) != n:
            raise ValueError("Value Overrun")
        self.pos += n
        return chunk

def repacks(bits, fmt):
    reader = BitReader(bits)
    return _repack_fmt(reader, fmt)

def _repack_fmt(reader, fmt):
    i = 0
    out = []
    L = len(fmt)

    while i < L:
        count = 0
        while i < L and fmt[i].isdigit():
            count = count * 10 + int(fmt[i])
            i += 1
        if count == 0:
            count = 1

        if i >= L:
            raise SyntaxError("Unexpected format termination")

        token = fmt[i]
        token_bpo = 0 # Bytes per Object
        if token in ('i', 'f'):
            token_bpo = 4
        elif token in ('s',):
            token_bpo = 1
        if token in ('i', 'f'):
            bits = reader.take(token_bpo*8*count)
            b = bytearray()
            for k in range(token_bpo*count):
                b.append(sum((bits[k*8 + j] << j) for j in range(8)))
            out.extend(struct.unpack(f"{count}{token}", b))
            i += 1
        elif token == 's':
            bits = reader.take(token_bpo*8*count)
            b = bytearray()
            for k in range(token_bpo*count):
                b.append(sum((bits[k*8 + j] << j) for j in range(8)))
            out.append(b.decode(errors='replace'))
            i += 1
        elif token == '[':
            depth = 0
            j = i + 1
            while j < L:
                if fmt[j] == '[':
                    depth += 1
                elif fmt[j] == ']':
                    if depth == 0:
                        break
                    depth -= 1
                j += 1
            if j >= L:
                raise SyntaxError("Unmatched '[' in format")

            inner_fmt = fmt[i+1:j]

            for _ in range(count):
                out.append(_repack_fmt(reader, inner_fmt))

            i = j + 1
        else:
            raise SyntaxError("Unexpected format token")

    return tuple(out)

def synthesize_CNF(result_binary, K, solver_name="glucose4"):
    vpool = IDPool()
    cnf = []

    num_inputs = len(result_binary[0][0])
    num_outputs = len(result_binary[0][1])

    sel = {}
    for i in range(num_inputs):
        for k in range(K):
            for j in range(num_outputs):
                vars_ = [
                    vpool.id(f"sel_{i}_{k}_{j}_0"),
                    vpool.id(f"sel_{i}_{k}_{j}_1"),
                    vpool.id(f"sel_{i}_{k}_{j}_2"),
                ]
                sel[i, k, j] = vars_
                cnf.extend(CardEnc.equals(vars_, bound=1, vpool=vpool).clauses)

    and_val = {}
    or_val = {}
    for c_idx, (inp_bits, out_bits) in enumerate(result_binary):
        for j in range(num_outputs):
            or_var = vpool.id(f"or_{c_idx}_{j}")
            or_val[c_idx, j] = or_var

        for j in range(num_outputs):
            and_vars_for_or = []
            for k in range(K):
                a = vpool.id(f"and_{c_idx}_{k}_{j}")
                and_val[c_idx, k, j] = a
                and_vars_for_or.append(a)

                for i in range(num_inputs):
                    s_unused, s_pos, s_neg = sel[i, k, j]
                    x = inp_bits[i]

                    if x == 0:
                        cnf.append([-a, -s_pos])
                    if x == 1:
                        cnf.append([-a, -s_neg])
                match_clause = []
                for i in range(num_inputs):
                    s_unused, s_pos, s_neg = sel[i, k, j]
                    x = inp_bits[i]

                    if x == 0:
                        match_clause.append(s_pos)
                    else:
                        match_clause.append(s_neg)

                match_clause.append(a)
                cnf.append(match_clause)
            or_var = or_val[c_idx, j]
            cnf.append([-or_var] + and_vars_for_or)
            for a in and_vars_for_or:
                cnf.append([-a, or_var])

            if out_bits[j] == 1:
                cnf.append([or_var])
            if out_bits[j] == 0:
                cnf.append([-or_var])
    with Solver(name=solver_name) as s:
        for cl in cnf:
            s.add_clause(cl)
        sat = s.solve()
        if not sat:
            return None
        model = set(s.get_model())
    return sel, model

def find_minimal_circuit(result_binary, K_max):
    for K in range(1, K_max+1):
        res = synthesize_CNF(result_binary, K)
        if res is not None:
            sel, model = res
            return K, sel, model
    return None

def decode_circuit(sel, model, num_inputs, num_outputs, K):
    def is_true(var):
        return var in model

    clauses_per_output = [[] for _ in range(num_outputs)]
    for j in range(num_outputs):
        for k in range(K):
            lits = []
            for i in range(num_inputs):
                s_unused, s_pos, s_neg = sel[i, k, j]
                if is_true(s_pos):
                    lits.append((i, True))
                elif is_true(s_neg):
                    lits.append((i, False))
            if lits:
                clauses_per_output[j].append(lits)
    return clauses_per_output

def generate_python_function(clauses_per_output, func, fmt_in, fmt_out):
    def tab_split(func):
        return ["    " + line for line in inspect.getsource(func).splitlines()]
    lines = []
    lines.append(f"def {func.__name__}({', '.join(inspect.getfullargspec(func).args)}):")
    lines.append( "    import struct")
    lines.append(f"    fmt_in = \"{fmt_in}\"")
    lines.append(f"    fmt_out = \"{fmt_out}\"")
    lines.extend(tab_split(bit_unpack))
    lines.extend(tab_split(unpack))
    lines.extend(tab_split(unpacks))
    lines.extend(tab_split(BitReader))
    lines.extend(tab_split(_repack_fmt))
    lines.extend(tab_split(repacks))
    lines.append(f"    x_bits = unpacks(({', '.join(inspect.getfullargspec(func).args)},), fmt_in)")
    lines.append( "    out = []")
    for j, clauses in enumerate(clauses_per_output):
        if not clauses:
            lines.append("    y = 0")
        else:
            or_terms = []
            for clause in clauses:
                and_terms = []
                for (i, pos) in clause:
                    if pos:
                        and_terms.append(f"(x_bits[{i}] == 1)")
                    else:
                        and_terms.append(f"(x_bits[{i}] == 0)")
                and_expr = " and ".join(and_terms) if and_terms else "True"
                or_terms.append(f"({and_expr})")
            or_expr = " or ".join(or_terms) if or_terms else "False"
            lines.append(f"    y = int({or_expr})")
        lines.append("    out.append(y)")
    lines.append( "    return repacks(out, fmt_out)")
    return "\n".join(lines)

def fibb(x: int): # Fibonacci, zero indexed
    if x == 0 or x == 1: return x
    return fibb(x-1) + fibb(x-2)

def ex_hash(i: int, s: str, d: float):
    h = 0
    h ^= i & 0xe52c6b23
    for b in s.encode("utf-8"):
        h = ((h << 5) - h) ^ b

    h ^= int(d * 4207807) & 0x05ed68ff
    return h & 0x888ac308

function = fibb
fmt_in = "i"
fmt_out = "i"
inputs = [
    set(range(0,11)),
    #{''.join(p) for p in itertools.product(['1','2','3','4'], repeat=4)},
    #set(np.arange(0, 10, 0.1)),
    ]

result = []
for inp in itertools.product(*inputs):
    result.append((inp, (function(*inp),)))

n = fmt_bytes(fmt_in)
m = fmt_bytes(fmt_out)

result_binary = []
for inp, out in result:
    result_binary.append((unpacks(inp, fmt_in), unpacks(out, fmt_out)))

K, sel, model = find_minimal_circuit(result_binary, K_max=10)
clauses = decode_circuit(sel, model, n, m, K)
code = generate_python_function(clauses, function, fmt_in, fmt_out)
print(code)
