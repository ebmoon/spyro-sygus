import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class SoundnessOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_program(self, program):
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]
        functions = [cmd.accept(self) for cmd in program.define_function_commands]
        constraints = [cmd.accept(self) for cmd in program.define_constraint_commands]

        return (variables, functions, constraints)

class SoundnessOracle(object):

    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = SoundnessOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("sygus-grammar-cons", "any-const")
        self.solver.setOption("tlimit", TIMEOUT)
        
        variables, functions, constraints = ast.accept(self.__initializer)
        
        self.variables = variables
        self.constraints = constraints
        self.functions = functions

    # Input : Candadate specification as CVC5 term
    # Output : Counterexample as CVC5 term
    def check_soundness(self, spec):
        self.solver.push()

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
        

