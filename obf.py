import inspect
import itertools
from pyeda.inter import *

def ast_parse(ast, var): # ast is tuple
    if type(var) is not str: raise Exception("Invalid variable")
    if type(ast) is not tuple: raise Exception("AST not tuple")
    if type(ast[0]) is not str: raise Exception("AST does not start with str op")
    if ast[0] == 'lit':
        return f"({'not ' if ast[1]<0 else ''}{var}[{abs(ast[1])-1}])"
    if ast[0] in ('and', 'or'):
        return "(" + f" {ast[0]} ".join([ast_parse(x, var) for x in ast[1:]]) + ")"
    raise Exception(f"Unaccounted for node: {ast}")

def bits(x, w):
    if type(x) is tuple and type(w) is tuple and len(x) == len(w):
        return tuple([bits(x[i],w[i]) for i in range(len(x))])
    return tuple((x >> i) & 1 for i in range(w))

def f(x): # Fibonacci, zero indexed
    if x == 0 or x == 1: return x
    return f(x-1) + f(x-2)

function = f
inputs = [
    set(range(0,11)),
    ]

result = []
for input in itertools.product(*inputs):
    result.append((input, function(*input)))
output_type = type(result[0][1])

n = tuple([max(out).bit_length() for out in inputs]) #Input bit length
m = max(out for (_, out) in result).bit_length() #Output bit length/Number of circuits

result_binary = []
for input, output in result:
    result_binary.append((sum(bits(input, n), ()), bits(output, m)))

dicts = []
for i in range(m):
    d = {}
    for instance in result_binary:
        d[instance[0]] = instance[1][i]
    dicts.append(d)

tt_strings = []
rows = list(itertools.product([0,1], repeat=sum(n)))
for i in range(m):
    tt_list = []
    for row in rows:
        if row in dicts[i]:
            tt_list.append(str(dicts[i][row]))
        else:
            tt_list.append("-")
    tt_string = "".join(tt_list)
    tt_strings.append(tt_string)

exprvar = 'x'
tables = [truthtable(exprvars(exprvar, sum(n)), tt) for tt in tt_strings]
expressions = espresso_tts(*tables)

statements = [ast_parse(x.to_ast(), exprvar) for x in expressions]

code = f"def {function.__name__}{str(inspect.signature(function))}:\n    {exprvar} = tuple((x >> i) & 1 for i in reversed(range({sum(n)})))\n    y = []"
for i in range(m):
    code += f"\n    y.append({statements[i]})"
code += "\n    r = 0"
code += "\n    for b in reversed(y):"
code += "\n        r = (r << 1) | b"
code += "\n    return r"

print(code)
