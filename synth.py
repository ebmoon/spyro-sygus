from z3 import *
from spyro_ast import *
from z3_util import *
from unrealizable import *

class SynthesisOracleInitializer(BaseInitializer):
    
    def __init__(self, solver, pos, neg):
        super().__init__(solver, pos, neg)

    def visit_program(self, program):
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

class SynthesisUnrealizabilityChecker(BaseUnrealizabilityChecker):

    def __init__(self, solver, pos, neg):
        super().__init__(solver, pos, neg)

    def visit_program(self, program):
        [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        start_sem = sem_functions[0]
        realizable = Function("realizable", BoolSort())

        head = realizable()
        
        body_arg = [item for e_pos in self.pos for item in e_pos]
        body_arg += [item for e_neg in self.neg for item in e_neg]
        body_arg += [True] * len(self.pos)
        body_arg += [False] * len(self.neg)

        body = start_sem(*body_arg)

        self.solver.register_relation(realizable)
        self.solver.add_rule(head, body)

        return realizable

class SynthesisOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def synthesize(self, pos, neg):
        solver = Fixedpoint()
        checker = SynthesisUnrealizabilityChecker(solver, pos, neg)
        realizable = self.ast.accept(checker)

        if solver.query(realizable) == sat:
            solver = Fixedpoint()
            initializer = SynthesisOracleInitializer(solver, pos, neg) 
            realizable = self.ast.accept(initializer) 

            if solver.query(realizable) == sat:
                answer = solver.get_answer().arg(1).arg(0).arg(0)
                return answer.arg(0)
            else:
                # should not happen
                raise NotImplementedError
        else:
            return None