import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class ImplicationOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_program(self, program):
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]

        return (variables)

class ImplicationOracle(object):

    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = ImplicationOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("sygus-grammar-cons", "any-const")
        self.solver.setOption("tlimit", TIMEOUT)
        
        variables = ast.accept(self.__initializer)
        
        self.variables = variables

    # Input : Candadate specification as CVC5 term
    # Output : Counterexample as CVC5 term
    def check_implication(self, phi_list, spec):
        self.solver.push()

        for phi in phi_list:
            phi_spec = self.solver.mkTerm(Kind.APPLY_UF, phi, *self.variables)
            self.solver.addSygusConstraint(phi_spec)

        constraint_spec = self.solver.mkTerm(Kind.APPLY_UF, spec, *self.variables)
        spec_neg = self.solver.mkTerm(Kind.NOT, constraint_spec)
        self.solver.addSygusConstraint(spec_neg)

        if self.solver.checkSynth().hasSolution():
            soln = self.solver.getSynthSolutions(self.variables)
            self.solver.pop()
            return soln
        else:
            self.solver.pop()
            return None