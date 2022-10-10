from z3 import *
from spyro_ast import *
from z3_util import *

class SynthesisOracleInitializer(BaseInitializer):
    
    def __init__(self, solver, pos, neg):
        super().__init__(solver)

        self.pos = pos
        self.neg = neg

    def visit_program(self, program):
        # Set logic of the solver

        [target_function.accept(self) for target_function in program.target_functions]
        nonterminals, sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        start = nonterminals[0]
        start_sem = sem_functions[0]
        witness = Const("witness", start)
        realizable = Function("realizable", start, BoolSort())

        head = realizable(witness)
        body = []
        
        for e_pos in self.pos:
            body.append(start_sem(witness, *e_pos, True))
        
        for e_neg in self.neg:
            body.append(start_sem(witness, *e_neg, False))

        self.solver.declare_var(witness)
        self.solver.register_relation(realizable)
        self.solver.add_rule(head, body)

        return realizable

class SynthesisOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def synthesize(self, pos, neg):
        solver = Fixedpoint()
        initializer = SynthesisOracleInitializer(solver, pos, neg) 
        realizable = self.ast.accept(initializer)

        if solver.query(realizable) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)
            return answer.arg(0)
        else:
            return None