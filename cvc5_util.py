from cvc5 import Kind
from collections import defaultdict
from spyro_ast import ASTVisitor
from abc import ABC

TIMEOUT = str(300)

reserved_ids = {
    'true': lambda solver: solver.mkTrue(),
    'false': lambda solver: solver.mkFalse()
}

MINUS = '-'
reserved_functions = {
    '<': Kind.LT,
    '<=': Kind.LEQ,
    '>': Kind.GT,
    '>=': Kind.GEQ,
    '=': Kind.EQUAL,
    'distinct': Kind.DISTINCT,
    'ite': Kind.ITE,
    '+': Kind.ADD,
    '*': Kind.MULT,
    '-': Kind.SUB,
    'or': Kind.OR,
    'and': Kind.AND,
    'not': Kind.NOT
}

kind_dict = defaultdict(lambda: Kind.APPLY_UF)
for k, v in reserved_functions.items():
    kind_dict[k] = v

class BaseInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        self.cxt_variables = {}
        self.cxt_functions = {}
        self.current_grammar = None
        self.current_head_symbol = None

    def visit_sort_expression(self, sort_expression):
        identifier = sort_expression.identifier
        if (identifier == "Int"):
            return self.solver.getIntegerSort()
        elif (identifier == "Bool"):
            return self.solver.getBooleanSort()
        else:
            raise NotImplementedError

    def visit_identifier_term(self, identifier_term):
        if identifier_term.identifier in reserved_ids:
            return reserved_ids[identifier_term.identifier](self.solver)
        else:
            return self.cxt_variables[identifier_term.identifier]

    def visit_numeral_term(self, numeral_term):
        return self.solver.mkInteger(numeral_term.value)

    def visit_function_application_term(self, function_application_term):
        kind = kind_dict[function_application_term.identifier]
        arg_terms = [arg.accept(self) for arg in function_application_term.args]
        if function_application_term.identifier == MINUS and len(arg_terms) == 1:
            return self.solver.mkTerm(Kind.NEG, *arg_terms)
        elif function_application_term.identifier in reserved_functions:
            return self.solver.mkTerm(kind, *arg_terms)
        else:
            return self.solver.mkTerm(kind, self.cxt_functions[function_application_term.identifier], *arg_terms)

    def visit_constant_term(self, constant_term):
        self.current_grammar.addAnyConstant(self.current_head_symbol)

    def visit_production_rule(self, production_rule):
        head_symbol_term = self.cxt_variables[production_rule.head_symbol]
        self.current_head_symbol = head_symbol_term

        rule_terms = [rule.accept(self) for rule in production_rule.terms]
        rule_terms = [term for term in rule_terms if term != None]

        self.current_head_symbol = None        

        return rule_terms

    def visit_grammar(self, grammar):
        current_cxt = self.cxt_variables.copy()

        nonterminal_vars = []
        for identifier, sort in grammar.nonterminals:
            nonterminal_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt_variables[identifier] = nonterminal_var
            nonterminal_vars.append(nonterminal_var)

        g = self.solver.mkGrammar(current_cxt.values(), nonterminal_vars)
        self.current_grammar = g

        for head_symbol, rule in grammar.rules.items():
            g.addRules(self.cxt_variables[head_symbol], rule.accept(self))

        self.current_grammar = None
        self.cxt_variables = current_cxt

        return g

    def visit_set_logic_command(self, set_logic_command):
        self.solver.setLogic(set_logic_command.logic)

    def visit_define_variable_command(self, define_variable_command):
        sort = define_variable_command.sort.accept(self)

        current_cxt = self.cxt_variables
        self.cxt_variables = {}

        g = define_variable_command.grammar.accept(self)
        term = self.solver.synthFun(define_variable_command.identifier, [], sort, g)

        self.cxt_variables = current_cxt        
        self.cxt_variables[define_variable_command.identifier] = term

        return term

    def visit_define_constraint_command(self, define_constraint_command):
        constraint = define_constraint_command.term.accept(self)
        self.solver.addSygusConstraint(constraint)

        return constraint

    def visit_define_generator_command(self, define_generator_command):
        g = define_generator_command.grammar.accept(self)
        return self.solver.synthFun("spec", self.cxt_variables.values(), self.solver.getBooleanSort(), g)

    def visit_define_function_command(self, define_function_command):
        current_cxt = self.cxt_variables.copy()

        args = []
        for identifier, sort in define_function_command.args:
            arg_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt_variables[identifier] = arg_var
            args.append(arg_var)
        
        sort = define_function_command.sort.accept(self)
        term = define_function_command.term.accept(self)

        f = self.solver.defineFun(define_function_command.identifier, args, sort, term)

        self.cxt_variables = current_cxt
        self.cxt_functions[define_function_command.identifier] = f

        return f

def define_fun_to_string(f, params, body):
    sort = f.getSort()
    if sort.isFunction():
        sort = f.getSort().getFunctionCodomainSort()
    result = "(define-fun " + str(f) + " ("
    for i in range(0, len(params)):
        if i > 0:
            result += " "
        result += "(" + str(params[i]) + " " + str(params[i].getSort()) + ")"
    result += ") " + str(sort) + " " + str(body) + ")"
    return result

def print_synth_solutions(f, sol):
    result = "(\n"
    params = []
    body = sol
    if sol.getKind() == Kind.LAMBDA:
        params += sol[0]
        body = sol[1]
        result += "  " + define_fun_to_string(f, params, body) + "\n"
    result += ")"
    print(result)

cnt = 0
def make_fresh_spec(solver, f, sol):
    global cnt

    params = list(sol[0])
    body = sol[1]
    sort = f.getSort().getFunctionCodomainSort()

    spec = solver.defineFun(f"spec{cnt}", params, sort, body)
    cnt += 1

    return spec