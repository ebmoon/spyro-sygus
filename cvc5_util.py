from cvc5 import Kind
from collections import defaultdict

reserved = {
    '<': Kind.LT,
    '<=': Kind.LEQ,
    '>': Kind.GT,
    '>=': Kind.GEQ,
    '=': Kind.EQUAL,
    'distinct': Kind.DISTINCT,
    'ite': Kind.ITE,
    '+': Kind.ADD,
    '*': Kind.MULT,
    '-': Kind.SUB
}

kind_dict = defaultdict(lambda: Kind.APPLY_UF)
for k, v in reserved.items():
    kind_dict[k] = v