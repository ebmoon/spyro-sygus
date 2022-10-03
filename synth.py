import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class SynthesisOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_define_variable_command(self, define_variable_command):
        sort = define_variable_command.sort.accept(self)
        term = self.solver.mkVar(sort, define_variable_command.identifier)
      
        self.cxt_variables[define_variable_command.identifier] = term

        return term

    def visit_program(self, program):
        # Set logic of the solver
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]
        spec = program.generator.accept(self)

        return (variables, spec)

class SynthesisOracle(object):

    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = SynthesisOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("tlimit", TIMEOUT)
        
        variables, spec = ast.accept(self.__initializer)
        
        self.variables = variables
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

    def make_true_spec(self):
        bool_sort = self.solver.getBooleanSort()
        true_term = self.solver.mkTrue()
        return self.solver.defineFun("spec", self.variables, bool_sort, true_term)

    def synthesize(self):
        if self.solver.checkSynth().hasSolution():
            return self.solver.getSynthSolution(self.spec)
        else:
            return None

        

