from z3 import *
from spyro_ast import *
from z3_util import *
from synth import SynthesisOracleInitializer

class PrecisionOracleInitializer(BaseInitializer):
    
    def __init__(self, solver, phi_list, phi, pos, neg):
        super().__init__(solver, pos, neg)

        self.phi_list = phi_list
        self.phi = phi

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

class PrecisionUnrealizabilityChecker(BaseUnrealizabilityChecker):

    def __init__(self, phi_list, phi, solver, pos, neg):
        super().__init__(solver, pos, neg)

        self.phi_list = phi_list
        self.phi = phi

        self.num_examples += 1

    def visit_program(self, program):
        functions = [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        variable_sorts = [variable.sort() for variable in self.variables]
        variables = [variable for _, var_list in self.variables for variable in var_list]

        start_sem = sem_functions[0]
        imprecise = Function("imprecise", *variable_sorts, BoolSort())

        head = imprecise(*self.variables)
        body = []

        body_arg = [item for e_pos in self.pos for item in e_pos]
        body_arg += [item for e_neg in self.neg for item in e_neg]
        body_arg += variables
        body_arg += [True] * len(self.pos)
        body_arg += [False] * len(self.neg)
        body_arg += [False]

        body.append(self.phi(variables))
        body.append(start_sem(*body_arg))

        for prev_phi in self.phi_list:
            body.append(prev_phi(variables))
       
        self.solver.register_relation(imprecise)
        self.solver.add_rule(head, body)

        return imprecise, len(self.variables), len(variables)


class PrecisionOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def check_precision(self, phi_list, phi, pos, neg):
        solver = Fixedpoint()
        initializer = PrecisionOracleInitializer(solver, phi_list, phi, pos, neg) 
        variables, start, num_variables = self.ast.accept(initializer)

        if solver.query(imprecise) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)
            e_neg = []
            for i in range(num_variables):
                e_neg.append(answer.arg(start + i))
            
            e_neg = e_neg[::-1]

            solver = Fixedpoint()
            initializer = SynthesisOracleInitializer(solver, pos, neg + [e_neg]) 
            realizable = self.ast.accept(initializer)
            
            if solver.query(realizable) == sat:
                answer = solver.get_answer().arg(1).arg(0).arg(0)
                phi = answer.arg(0)
                return e_neg, phi
            else:
                # should not happen
                raise NotImplementedError
        else:
            return None, None