from cvc5 import Kind
from collections import defaultdict

TIMEOUT = str(300000)

reserved_ids = {
    'true': lambda solver: solver.mkTrue(),
    'false': lambda solver: solver.mkFalse()
}

MINUS = '-'
reserved_functions = {
    '<': Kind.LT,
    '<=': Kind.LEQ,
    '>': Kind.GT,
    '>=': Kind.GEQ,
    '=': Kind.EQUAL,
    'distinct': Kind.DISTINCT,
    'ite': Kind.ITE,
    '+': Kind.ADD,
    '*': Kind.MULT,
    '-': Kind.SUB,
    'or': Kind.OR,
    'and': Kind.AND,
    'not': Kind.NOT
}

kind_dict = defaultdict(lambda: Kind.APPLY_UF)
for k, v in reserved_functions.items():
    kind_dict[k] = v

def define_fun_to_string(f, params, body):
    sort = f.getSort()
    if sort.isFunction():
        sort = f.getSort().getFunctionCodomainSort()
    result = "(define-fun " + str(f) + " ("
    for i in range(0, len(params)):
        if i > 0:
            result += " "
        result += "(" + str(params[i]) + " " + str(params[i].getSort()) + ")"
    result += ") " + str(sort) + " " + str(body) + ")"
    return result

def print_synth_solutions(f, sol):
    result = "(\n"
    params = []
    body = sol
    if sol.getKind() == Kind.LAMBDA:
        params += sol[0]
        body = sol[1]
        result += "  " + define_fun_to_string(f, params, body) + "\n"
    result += ")"
    print(result)