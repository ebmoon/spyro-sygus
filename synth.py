from z3 import *
from spyro_ast import *
from z3_util import *
from unrealizable import *
from cvc5_util import *
import cvc5

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
        self.synthesizer = cvc5.Solver()
        self.ast = ast

        self.synthesizer.setOption("sygus", "true")
        self.synthesizer.setOption("incremental", "true")

        initializer = SynthesisOracleInitializer(self.synthesizer)
        self.spec = ast.accept(initializer)

        self.solver.push(2)

        self.new_pos = []
        self.neg_may = []

    def add_positive_example(self, e):
        self.solver.pop()

        term = self.solver.mkTerm(Kind.APPLY_UF, self.spec, *e)
        
        self.solver.addSygusConstraint(term)
        self.new_pos.append(term)

        self.solver.push()

        for e_term in self.neg_may:
            self.solver.addSygusConstraint(e_term)

    def add_negative_example(self, e):
        term = self.solver.mkTerm(Kind.APPLY_UF, self.spec, *e)
        neg_term = self.solver.mkTerm(Kind.NOT, term)
        
        self.solver.addSygusConstraint(neg_term)
        self.neg_may.append(neg_term)

    def freeze_negative_example(self):
        self.solver.pop()

        for e_term in self.neg_may:
            self.solver.addSygusConstraint(e_term)
        
        self.neg_may = []

        self.solver.push()

    def clear_negative_may(self):
        self.solver.pop()     
        
        self.neg_may = []

        self.solver.push()

    def clear_negative_example(self):
        self.solver.pop(2)

        for e_term in self.new_pos:
            self.solver.addSygusConstraint(e_term)
        
        self.new_pos = []
        self.neg_may = []

        self.solver.push(2)

    def synthesize(self):
        if self.solver.checkSynth().hasSolution():
            return self.solver.getSynthSolution(self.spec)
        else:
            return None

    def synthesize(self, pos, neg):
        solver = Fixedpoint()
        checker = SynthesisUnrealizabilityChecker(solver, pos, neg)
        realizable = self.ast.accept(checker)

        if solver.query(realizable) == sat:
            print("realizable, try synthesis")

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