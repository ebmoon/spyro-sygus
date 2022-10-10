from z3 import *
from collections import defaultdict
from spyro_ast import ASTVisitor, SortExpression
from abc import ABC
import functools

TIMEOUT = str(300)

reserved_ids = {
    'true': True,
    'false': False
}

MINUS = '-'
ITE = 'ite'
reserved_functions = {
    '<': lambda x, y: x < y,
    '<=': lambda x, y: x <= y,
    '>': lambda x, y: x > y,
    '>=': lambda x, y: x >= y,
    '=': lambda x, y: x == y,
    'distinct': lambda x, y: x != y,
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

def join(t1, t2):
    ret = []
    for premise1, val1 in t1:
        for premise2, val2 in t2:
            ret.append((premise1 + premise2, val1 + [val2]))

    return ret

def foldl(func, acc, xs):
  return functools.reduce(func, xs, acc)

class BaseInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        
        self.cxt_sorts = reserved_sorts.copy()
        self.cxt_nonterminals = {}
        self.cxt_variables = {}
        self.cxt_functions = {}
        
        self.variables = []
        self.current_nonterminal = None
        self.rule_dict = {}

        self.var_cnt = 0

    def __fresh_var(self, sort):
        variable = Const(f'{str(sort).lower()}_{self.var_cnt}', sort)
        self.var_cnt += 1

        return variable

    def visit_sort_expression(self, sort_expression):
        if sort_expression.identifier in self.cxt_sorts:
            return self.cxt_sorts[sort_expression.identifier]
        elif sort_expression.identifier in self.cxt_nonterminals:
            return self.cxt_nonterminals[sort_expression.identifier][1]
        else:
            raise NotImplementedError

    def visit_identifier_term(self, identifier_term):
        if identifier_term.identifier in reserved_ids:
            return [([], reserved_ids[identifier_term.identifier])]
        else:
            return [([], self.cxt_variables[identifier_term.identifier])]

    def visit_numeral_term(self, numeral_term):
        return [([], numeral_term.value)]

    def visit_function_application_term(self, function_application_term):
        arg_terms = [arg.accept(self) for arg in function_application_term.args]
        if function_application_term.identifier == ITE and len(arg_terms) == 3:
            branch_condition = arg_terms[0][0][1]
            true_branch = [(premise + [branch_condition], val) for premise, val in arg_terms[1]]
            false_branch = [(premise + [Not(branch_condition)], val) for premise, val in arg_terms[2]]
            return true_branch + false_branch
        elif function_application_term.identifier == MINUS and len(arg_terms) == 1:
            return [(premise, -val) for premise, val in arg_terms[0]]
        elif function_application_term.identifier in reserved_functions:
            args_join = foldl(join, [([], [])], arg_terms)
            fn = reserved_functions[function_application_term.identifier]
            return [(premise, fn(*args)) for premise, args in args_join]
        else:
            args_join = foldl(join, [([], [])], arg_terms)
            fn = self.cxt_functions[function_application_term.identifier]
            return [(premise, fn(*args)) for premise, args in args_join]

    def visit_syntactic_rule(self, syntactic_rule):
        for production in syntactic_rule.productions:
            rule = production.accept(self)
            self.current_nonterminal.declare(*rule)

    def visit_production_rule(self, production_rule):
        head_symbol = production_rule.head_symbol
        sorts = production_rule.sorts

        self.rule_dict[head_symbol] = sorts

        sorts = [sort.accept(self) for sort in production_rule.sorts]
        args = [(f'{head_symbol}_{i}', sort) for i, sort in enumerate(sorts)]

        return [head_symbol] + args

    def visit_semantic_rule(self, semantic_rule):
        symbol = semantic_rule.nonterminal
        sort, nonterminal, sem_function = self.cxt_nonterminals[symbol]
        match_symbol, body, term_variables, ret_variables = semantic_rule.match.accept(self)

        current_cxt_variables = self.cxt_variables.copy()
        for i, term_variable in enumerate(term_variables):
            self.cxt_variables[str(term_variable)] = ret_variables[i]
        
        premise, term = semantic_rule.term.accept(self)[0]
        
        self.cxt_variables = current_cxt_variables

        constructor = getattr(nonterminal, match_symbol)
        match_term = constructor(*term_variables) if len(term_variables) > 0 else constructor
        # print(match_term, self.variables, term)
        head = sem_function(match_term, *self.variables, term)

        if len(body) > 0:
            self.solver.add_rule(head, body)
        else:
            self.solver.add_rule(head)

    def visit_production_match(self, production_match):
        head_symbol = production_match.identifier
        variables = production_match.variables
        sorts = self.rule_dict[head_symbol]

        body = []
        ret_variables = []
        term_variables = []
        for i, symbol in enumerate(variables):
            term_sort = sorts[i]
            term_variable, _ = self.define_new_variable(symbol, term_sort)
            term_variables.append(term_variable)
            if str(term_sort) in self.cxt_nonterminals:
                ret_sort, nonterminal, sem_function = self.cxt_nonterminals[str(term_sort)]
                ret_variable, _ = self.define_new_variable(f'r_{head_symbol}_{i}', ret_sort)
                body.append(sem_function(term_variable, *self.variables, ret_variable))
                ret_variables.append(ret_variable)
            else:
                ret_variables.append(term_variable)

        return (head_symbol, body, term_variables, ret_variables)

    def visit_declare_language_command(self, declare_language_command):
        nonterminals = declare_language_command.nonterminals
        syntactic_rules = declare_language_command.syntactic_rules

        current_cxt_sorts = self.cxt_sorts.copy()

        nonterminal_datatypes = []
        for symbol, sort in nonterminals:
            dt = Datatype(symbol)

            self.cxt_sorts[symbol] = dt
            nonterminal_datatypes.append(dt)

        for i, syntactic_rule in enumerate(syntactic_rules):
            self.current_nonterminal = nonterminal_datatypes[i]
            syntactic_rule.accept(self)
            self.current_nonterminal = None

        self.cxt_sorts = current_cxt_sorts

        var_sorts = [variable.sort() for variable in self.variables]
        datatypes = CreateDatatypes(nonterminal_datatypes)
        sem_functions = []
        for i, (symbol, sort) in enumerate(nonterminals):
            sort = sort.accept(self)
            semantics_function = Function(f'{symbol}.Sem', datatypes[i], *var_sorts, sort, BoolSort())
            self.cxt_nonterminals[symbol] = (sort, datatypes[i], semantics_function)
            sem_functions.append(semantics_function)

            self.solver.register_relation(semantics_function)

        return datatypes, sem_functions

    def visit_declare_semantics_command(self, declare_semantics_command):
        for semantic_rule in declare_semantics_command.semantic_rules:
            semantic_rule.accept(self)

    def define_new_variable(self, identifier, sort):
        if identifier not in self.cxt_variables:
            if type(sort) == SortExpression:
                sort = sort.accept(self)
            variable = Const(identifier, sort)
            self.cxt_variables[identifier] = variable
            self.solver.declare_var(variable)
            return (variable, sort)
        else:
            variable = self.cxt_variables[identifier]
            return (variable, variable.sort())

    def visit_target_function_command(self, target_function_command):
        identifier = target_function_command.identifier
        inputs = target_function_command.inputs
        output_id, output_sort = target_function_command.output
        term = target_function_command.term

        input_sorts = []
        input_variables = []
        for input_id, input_sort in inputs:
            variable, sort = self.define_new_variable(input_id, input_sort)
            input_sorts.append(sort)
            input_variables.append(variable)

        output_variable, output_sort = self.define_new_variable(output_id, output_sort)

        function = Function(identifier, *input_sorts, output_sort, BoolSort())
        self.cxt_functions[identifier] = function
        self.solver.register_relation(function)

        rules = term.accept(self)
        for premise, value in rules:
            self.solver.add_rule(function(*input_variables, value), And(*premise))

        self.variables = input_variables + [output_variable]

        return function