import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class PrecisionOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_program(self, program):
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]
        functions = [cmd.accept(self) for cmd in program.define_function_commands]
        spec = program.generator.accept(self)

        constraint = self.solver.mkTerm(Kind.APPLY_UF, spec, *variables)
        constraint_neg = self.solver.mkTerm(Kind.NOT, constraint)
        self.solver.addSygusConstraint(constraint_neg)

        return (variables, functions, spec)

class PrecisionOracle(object):

    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = PrecisionOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("sygus-grammar-cons", "any-const")
        self.solver.setOption("tlimit", TIMEOUT)
        
        variables, functions, spec = ast.accept(self.__initializer)
        
        self.variables = variables
        self.functions = functions
        self.spec = spec

        self.new_pos = []
        self.neg_may = []

        self.solver.push(1)
        self.solver.push(2)

    def add_positive_example(self, e):
        self.solver.pop(2)

        term = self.solver.mkTerm(Kind.APPLY_UF, self.spec, *e)
        
        self.addSygusConstraint(term)
        self.new_pos.append(term)

        self.solver.push(2)

        for e_term in self.neg_may:
            self.addSygusConstraint(e_term)

    def add_negative_example(self, e):
        term = self.solver.mkTerm(Kind.APPLY_UF, self.spec, *e)
        neg_term = self.solver.mkTerm(Kind.NOT, term)
        
        self.addSygusConstraint(neg_term)
        self.neg_may.append(neg_term)

    def freeze_negative_example(self):
        self.solver.pop(2)

        for e_term in self.neg_may:
            self.addSygusConstraint(e_term)
        
        self.neg_may = []

        self.solver.push(2)

    def clear_negative_example(self):
        self.solver.pop(2)
        self.solver.pop(1)

        for e_term in self.new_pos:
            self.addSygusConstraint(e_term)        
        
        self.new_pos = []

        self.solver.push(1)
        self.solver.push(2)

    def check_precision(self, spec):
        self.solver.push(3)
        
        constraint_spec = self.solver.mkTerm(Kind.APPLY_UF, spec, *self.variables)
        self.solver.addSygusConstraint(constraint_spec)

        if self.solver.checkSynth().hasSolution():
            const_soln = self.solver.getSynthSolutions(self.variables)
            spec_soln = self.solver.getSynthSolution(self.spec)
            self.solver.pop(3)
            return (const_soln, spec_soln)
        else:
            self.solver.pop(3)
            return (None, None)

        

