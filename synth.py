from z3 import *
from spyro_ast import *
from z3_util import *

class SynthesisOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_program(self, program):
        # Set logic of the solver

        [target_function.accept(self) for target_function in program.target_functions]
        program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        print(self.solver.sexpr())

        return None

class SynthesisOracle(object):

    def __init__(self, ast):
        self.solver = Fixedpoint()
        self.ast = ast
        self.__initializer = SynthesisOracleInitializer(self.solver) 

        variables, spec = ast.accept(self.__initializer)

        self.solver.push(2)

        self.variables = variables
        self.spec = spec

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
        synthResult = self.solver.checkSynth()
        if synthResult.hasSolution():
            return self.solver.getSynthSolution(self.spec)
        else:
            return None
            
    def synthesize_next(self):
        synthResult = self.solver.checkSynthNext()
        if synthResult.hasSolution():
            return self.solver.getSynthSolution(self.spec)
        else:
            return None

        

