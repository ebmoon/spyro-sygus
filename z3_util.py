from z3 import *
from collections import defaultdict
from spyro_ast import ASTVisitor
from abc import ABC

TIMEOUT = str(300)

reserved_ids = {
    'true': True,
    'false': False
}

MINUS = '-'
reserved_functions = {
    '<': lambda x, y: x < y,
    '<=': lambda x, y: x <= y,
    '>': lambda x, y: x > y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'distinct': lambda x, y: x != y,
    'ite': IF,
    '+': lambda x, y: x + y,
    '*': lambda x, y: x * y,
    '-': lambda x, y: x - y,
    'or': Or,
    'and': And,
    'not': Not
}

reserved_sorts = {
    "Int": IntSort(),
    "Bool": BoolSort()
}

class BaseInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        
        self.cxt_sorts = reserved_sorts.copy()
        self.cxt_nonterminals = {}
        self.cxt_variables = {}
        self.cxt_functions = {}
        
        self.current_grammar = None
        self.current_head_symbol = None

        self.rule_dict = {}
        self.var_cnt = 0
        self.rule_cnt = 0

    def __fresh_var(self, sort):
        variable = Const(f'{str(sort).lower()}_{self.var_cnt}', sort)
        self.var_cnt += 1

        return variable

    def __fresh_rule_name(self):
        rule_name = f'rule_{self.rule_cnt}'
        self.rule_cnt += 1

        return rule_name

    def visit_sort_expression(self, sort_expression):
        if sort_expression.identifier in self.cxt_sorts:
            return self.cxt_sorts[sort_expression.identifier]
        else:
            raise NotImplementedError

    def visit_identifier_term(self, identifier_term):
        if identifier_term.identifier in reserved_ids:
            return reserved_ids[identifier_term.identifier]
        else:
            return self.cxt_variables[identifier_term.identifier]

    def visit_numeral_term(self, numeral_term):
        return numeral_term.value

    def visit_function_application_term(self, function_application_term):
        arg_terms = [arg.accept(self) for arg in function_application_term.args]
        if function_application_term.identifier == MINUS and len(arg_terms) == 1:
            return (- arg_terms[0])
        elif function_application_term.identifier in reserved_functions:
            fn = reserved_functions[function_application_term.identifier]
            return fn(*arg_terms)
        else:
            return self.cxt_functions[function_application_term.identifier](*arg_terms)

    def visit_constant_term(self, constant_term):
        sort = constant_term.sort
        variable = self.__fresh_var(sort)

        self.solver.declare_var(variable)
        rule_name = self.__fresh_rule_name()
        rule = self.current_head_symbol(*self.cxt_variables.values(), variable)
        self.add_rule(rule, rule_name)

        self.

        raise NotImplementedError
        # self.current_grammar.addAnyConstant(self.current_head_symbol)

    def visit_production_rule(self, production_rule):
        head_symbol_term = self.cxt_variables[production_rule.head_symbol]
        self.current_head_symbol = head_symbol_term

        rule_terms = [rule.accept(self) for rule in production_rule.terms]

        self.current_head_symbol = None        

        return rule_terms

    def declare_rules(head_symbol, rule):
        nonterminal = self.cxt_variables[head_symbol]
        
        for term in rule.terms:
            nonterminal.declare()

    def visit_grammar(self, grammar):
        current_cxt_sorts = self.cxt_sorts.copy()

        # Define datatypes

        nonterminals = []
        for identifier, sort in grammar.nonterminals:
            nonterminal = Datatype(head_symbol)
            self.cxt_sorts[identifier] = nonterminal
            nonterminals.append(nonterminal)

        for head_symbol, rule in grammar.rules.items():
            declare_rules(head_symbol, rule)

        datatypes = CreateDatatypes(*nonterminals)

        # Define semantics / semantic rules

        for identifier, sort in grammar.nonterminals:
            nonterminal_sem = Function(f'{identifier}.Sem', *vars_sort, sort.accept(self))
            self.cxt_variables[identifier] = nonterminal_sem
            nonterminal_sems.append(nonterminal_sem)

        vars_sort = [variable.sort() for variable in current_cxt.values()]
        nonterminal_sems = []

        self.solver.register_relation(nonterminal_sems)
            
            # g.addRules(f'{head_symbol}.Sem', self.cxt_variables[head_symbol], rule.accept(self))

        self.current_grammar = None
        self.cxt_sorts = current_cxt_sorts

        return nonterminal_sems

    def visit_define_variable_command(self, define_variable_command):
        sort = define_variable_command.sort.accept(self)

        variable = Const(define_variable_command.identifier, sort)

        # To-Do: After grammar

        g = define_variable_command.grammar.accept(self)
        term = self.solver.synthFun(define_variable_command.identifier, [], sort, g)

        self.cxt_variables = current_cxt        
        self.cxt_variables[define_variable_command.identifier] = term

        return variable

    def visit_define_constraint_command(self, define_constraint_command):
        constraint = define_constraint_command.term.accept(self)
        self.solver.addSygusConstraint(constraint)

        return constraint

    def visit_define_generator_command(self, define_generator_command):
        g = define_generator_command.grammar.accept(self)
        return Const("spec", g[0])

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