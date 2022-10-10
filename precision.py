from z3 import *
from spyro_ast import *
from z3_util import *

class PrecisionOracleInitializer(BaseInitializer):
    
    def __init__(self, solver, phi_list, phi, pos, neg):
        super().__init__(solver)

        self.phi_list = phi_list
        self.phi = phi
        self.pos = pos
        self.neg = neg

    def visit_program(self, program):
        # Set logic of the solver

        functions = [target_function.accept(self) for target_function in program.target_functions]
        nonterminals, sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        variable_sorts = [variable.sort() for variable in self.variables]

        start = nonterminals[0]
        start_sem = sem_functions[0]
        witness = Const("witness", start)
        imprecise = Function("imprecise", start, *variable_sorts, BoolSort())

        head = imprecise(witness, *self.variables)
        body = []
        
        body.append(start_sem(self.phi, *self.variables, True))
        body.append(start_sem(witness, *self.variables, False))

        for prev_phi in self.phi_list:
            body.append(start_sem(prev_phi, *self.variables, True))

        for e_pos in self.pos:
            body.append(start_sem(witness, *e_pos, True))
        
        for e_neg in self.neg:
            body.append(start_sem(witness, *e_neg, False))
        
        self.solver.declare_var(witness)
        self.solver.register_relation(imprecise)
        self.solver.add_rule(head, body)

        return imprecise, len(self.variables)

class PrecisionOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def check_precision(self, phi_list, phi, pos, neg):
        solver = Fixedpoint()
        initializer = PrecisionOracleInitializer(solver, phi_list, phi, pos, neg) 
        imprecise, num_variables = self.ast.accept(initializer)

        if solver.query(imprecise) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)

            e_neg = []
            for i in range(num_variables):
                e_neg.append(answer.arg(i))

            phi = answer.arg(num_variables)

            return e_neg[::-1], phi
        else:
            return None, None