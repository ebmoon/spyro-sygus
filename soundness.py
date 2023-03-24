from unrealizable import BaseUnrealizabilityChecker
from z3 import *
from spyro_ast import *
from z3_util import *

class SoundnessOracleInitializer(BaseUnrealizabilityChecker):
    
    def __init__(self, solver, phi):
        super().__init__(solver, [], [])

        self.phi = phi

    def visit_program(self, program):
        # Set logic of the solver

        functions = [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        variables = self.function_variables()
        variable_sorts = [variable.sort() for variable in variables]

        cex = Function("cex", *variable_sorts, BoolSort())

        head = cex(*variables)
        body = []
        
        for function in functions:
            body.append(function(*self.function_args[str(function)], True))
        
        body.append(Not(self.convert_term(self.phi)))

        self.solver.register_relation(cex)
        self.solver.add_rule(head, body)

        return cex, len(variables)

class SoundnessOracle(object):

    def __init__(self, ast, seed):
        self.ast = ast
        self.seed = seed

    def check_soundness(self, phi):
        solver = Fixedpoint()
        solver.set("spacer.random_seed", self.seed)
        initializer = SoundnessOracleInitializer(solver, phi) 
        cex, num_variables = self.ast.accept(initializer)

        solver.query(cex)
        if solver.query(cex) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)
            e_pos = []
            for i in range(num_variables):
                e_pos.append(answer.arg(i))

            return e_pos[::-1]
        else:
            return None