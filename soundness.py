import cvc5
from cvc5 import Kind

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

class SoundnessOracle(object):
    def __init__(self, functions):
        self.solver = cvc5.Solver()

        self.solver.setOption("produce-models", "true")

    def __make_term(self, cxt, t):
        if t[0] == 'Symbol':
            if t[1] in reserved:
                return reserved[t[1]]
            else:
                return cxt[t[1]]
        elif t[0] == 'Num':
            return self.solver.mkInteger(t[1])
        elif t[0] == 'App':
            subterms = [self.__make_term(cxt, subterm) for subterm in t[1:]]
            return self.solver.mkTerm(*subterms)
        else:
            raise Exception("Undefined term")

    def __make_function(f):
        raise NotImplemented
        

