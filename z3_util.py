from z3 import *
from collections import defaultdict
from spyro_ast import ASTVisitor, SortExpression
from abc import ABC
import functools

TIMEOUT = str(300)

reserved_ids = {
    'true': True,
    'false': False
}

MINUS = '-'
ITE = 'ite'
reserved_functions = {
    '<': lambda x, y: x < y,
    '<=': lambda x, y: x <= y,
    '>': lambda x, y: x > y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'distinct': lambda x, y: x != y,
    '+': lambda x, y: x + y,
    '*': lambda x, y: x * y,
    '-': lambda x, y: x - y,
    'or': Or,
    'and': And,
    'not': Not
}

reserved_sorts = {
    "Int": IntSort(),
    "Bool": BoolSort()
}

def join(t1, t2):
    ret = []
    for premise1, val1 in t1:
        for premise2, val2 in t2:
            ret.append((premise1 + premise2, val1 + [val2]))

    return ret

def foldl(func, acc, xs):
  return functools.reduce(func, xs, acc)

def convert_z3_to_cvc5(solver, term):
    if term.is_int():
        return solver.mkInteger(term.as_long())
    else:
        raise NotImplementedError