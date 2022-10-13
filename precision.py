from z3 import *
from spyro_ast import *
from z3_util import *
from synth import SynthesisOracleInitializer
from unrealizable import *

class PrecisionUnrealizabilityChecker(BaseUnrealizabilityChecker):

    def __init__(self, solver, pos, neg, phi_list, phi):
        super().__init__(solver, pos, neg)

        self.phi_list = phi_list
        self.phi = phi

        self.num_examples += 1

    def visit_program(self, program):
        functions = [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        variables = [variable for _, var_list in self.function_args.items() for variable in var_list]
        variable_sorts = [variable.sort() for variable in variables]

        start_sem = sem_functions[0]
        imprecise = Function("imprecise", *variable_sorts, BoolSort())

        head = imprecise(*variables)
        body = []

        body_arg = [item for e_pos in self.pos for item in e_pos]
        body_arg += [item for e_neg in self.neg for item in e_neg]
        body_arg += variables
        body_arg += [True] * len(self.pos)
        body_arg += [False] * len(self.neg)
        body_arg += [False]

        body.append(self.convert_term(self.phi))
        body.append(start_sem(*body_arg))

        for prev_phi in self.phi_list:
            body.append(self.convert_term(prev_phi))
       
        self.solver.register_relation(imprecise)
        self.solver.add_rule(head, body)

        return imprecise, len(variables)


class PrecisionOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def check_precision(self, phi_list, phi, pos, neg):
        solver = Fixedpoint()
        initializer = PrecisionUnrealizabilityChecker(solver, pos, neg, phi_list, phi) 
        imprecise, num_variables = self.ast.accept(initializer)

        if solver.query(imprecise) == sat:
            answer = solver.get_answer().arg(1).arg(0).arg(0)
            e_neg = []
            for i in range(num_variables):
                e_neg.append(answer.arg(i))
            
            e_neg = e_neg[::-1]

            print("imprecise, try synthesis")
            print(solver.get_answer())

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