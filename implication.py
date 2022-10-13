from unrealizable import BaseUnrealizabilityChecker
from z3 import *
from spyro_ast import *
from z3_util import *

class ImplicationOracleInitializer(BaseUnrealizabilityChecker):
    
    def __init__(self, solver, phi_list, phi):
        super().__init__(solver, [], [])

        self.phi_list = phi_list
        self.phi = phi

    def visit_program(self, program):
        # Set logic of the solver

        functions = [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        variable_sorts = [variable.sort() for variable in self.variables]

        start_sem = sem_functions[0]
        cex = Function("cex", *variable_sorts, BoolSort())

        head = cex(*self.variables)
        body = []
        
        for prev_phi in self.phi_list:
            body.append(self.convert_term(prev_phi))
        body.append(Not(self.convert_term(self.phi)))

        self.solver.register_relation(cex)
        self.solver.add_rule(head, body)

        return cex, len(self.variables)

class ImplicationOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def check_implication(self, phi_list, phi):
        solver = Fixedpoint()
        initializer = ImplicationOracleInitializer(solver, phi_list, phi) 
        cex, num_variables = self.ast.accept(initializer)

        solver.query(cex)
        if solver.query(cex) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)
            e_neg = []
            for i in range(num_variables):
                e_neg.append(answer.arg(i))

            return e_neg[::-1]
        else:
            return None