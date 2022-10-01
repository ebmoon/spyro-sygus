import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class SoundnessOracleInitializer(BaseInitializer):
    
    def __init__(self, solver):
        super().__init__(solver)

    def visit_program(self, program):
        # Set logic of the solver
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]
        functions = [cmd.accept(self) for cmd in program.define_function_commands]
        constraints = [cmd.accept(self) for cmd in program.define_constraint_commands]

        return (variables, constraints, functions)

class SoundnessOracle(object):

    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = SoundnessOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("sygus-grammar-cons", "any-const")
        
        variables, constraints, functions = ast.accept(self.__initializer)
        
        self.variables = variables
        self.constraints = constraints
        self.functions = functions

    # Input : Candadate specification as CVC5 term
    # Output : Counterexample as CVC5 term
    def check_soundness(self, spec):
        self.solver.push()

        spec_neg = self.solver.mkTerm(Kind.NOT, spec)
        self.solver.addSygusConstraint(spec_neg)

        if self.solver.checkSynth().hasSolution():
            return self.solver.getSynthSolutions(self.variables)
        else:
            return None

        self.solver.pop()
        

