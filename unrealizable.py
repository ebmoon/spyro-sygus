from z3 import *
from abc import ABC
from z3_util import *

class BaseUnrealizabilityChecker(BaseInitializer, ABC):
    
    def __init__(self, solver, pos, neg):
        super().__init__(solver, pos, neg)

        self.num_examples = len(pos) + len(neg)

    def visit_sort_expression(self, sort_expression):
        if sort_expression.identifier in self.cxt_sorts:
            return self.cxt_sorts[sort_expression.identifier]
        elif sort_expression.identifier in self.cxt_nonterminals:
            return self.cxt_nonterminals[sort_expression.identifier][0]
        else:
            raise NotImplementedError

    def visit_syntactic_rule(self, syntactic_rule):
        for production in syntactic_rule.productions:
            rule = production.accept(self)

    def visit_production_rule(self, production_rule):
        head_symbol = production_rule.head_symbol
        sorts = production_rule.sorts

        self.rule_dict[head_symbol] = sorts
       
    def visit_semantic_rule(self, semantic_rule):
        symbol = semantic_rule.nonterminal
        sort, sem_function = self.cxt_nonterminals[symbol]
        match_symbol, body, variables, ret_variable_copies = semantic_rule.match.accept(self)

        self.rule_term[match_symbol] = semantic_rule.term        

        terms = []
        for n in range(self.num_examples):
            current_cxt_variables = self.cxt_variables.copy()

            for symbol in variables:
                self.cxt_variables[symbol] = ret_variable_copies[symbol][n]
            
            premise, term = semantic_rule.term.accept(self)[0]
            terms.append(term)

            self.cxt_variables = current_cxt_variables

        head = sem_function(*self.variables, *terms)

        if len(body) > 0:
            self.solver.add_rule(head, body)
        else:
            self.solver.add_rule(head)

    def visit_production_match(self, production_match):
        head_symbol = production_match.identifier
        variables = production_match.variables
        sorts = self.rule_dict[head_symbol]

        self.rule_args[head_symbol] = variables

        body = []
        contexts = []
        ret_variable_copies = {symbol:[] for symbol in variables}

        for n in range(self.num_examples):
            current_cxt = self.cxt_variables.copy()

            for i, symbol in enumerate(variables):
                term_sort = sorts[i]
                ret_variable, _ = self.define_new_variable(f'{symbol}_{n}', term_sort)
                ret_variable_copies[symbol].append(ret_variable)

            self.cxt_variables = current_cxt

        for i, symbol in enumerate(variables):
            term_sort = sorts[i]
            ret_variables = ret_variable_copies[symbol]
            if str(term_sort) in self.cxt_nonterminals:
                ret_sort, sem_function = self.cxt_nonterminals[str(term_sort)]
                body.append(sem_function(*self.variables, *ret_variables))

        return (head_symbol, body, variables, ret_variable_copies)

    def visit_declare_language_command(self, declare_language_command):
        nonterminals = declare_language_command.nonterminals
        syntactic_rules = declare_language_command.syntactic_rules
           
        for syntactic_rule in syntactic_rules:
            syntactic_rule.accept(self)

        var_sorts = [variable.sort() for variable in self.variables]
        sem_functions = []
        for symbol, sort in nonterminals:
            sort = sort.accept(self)
            output_sorts = [sort] * self.num_examples

            semantics_function = Function(f'{symbol}.Sem', *var_sorts, *output_sorts, BoolSort())
            self.cxt_nonterminals[symbol] = (sort, semantics_function)
            sem_functions.append(semantics_function)

            self.solver.register_relation(semantics_function)

        return sem_functions

    def visit_declare_semantics_command(self, declare_semantics_command):
        for semantic_rule in declare_semantics_command.semantic_rules:
            semantic_rule.accept(self)

    def visit_target_function_command(self, target_function_command):
        identifier = target_function_command.identifier
        inputs = target_function_command.inputs
        output_id, output_sort = target_function_command.output
        term = target_function_command.term

        input_sorts = []
        input_variables = []
        input_copied_variables = []
        for input_id, input_sort in inputs:
            variable, sort = self.define_new_variable(input_id, input_sort)
            input_sorts.append(sort)
            input_variables.append(variable)

            for i in range(self.num_examples):
                variable, _ = self.define_new_variable(f'{input_id}_{i}', input_sort)
                input_copied_variables.append(variable)

        output_variable, output_sort = self.define_new_variable(output_id, output_sort)
        output_copied_variables = []
        for i in range(self.num_examples):
            variable, _ = self.define_new_variable(f'{output_id}_{i}', output_sort)
            output_copied_variables.append(variable)

        function = Function(identifier, *input_sorts, output_sort, BoolSort())
        self.cxt_functions[identifier] = function
        self.solver.register_relation(function)

        rules = term.accept(self)
        for premise, value in rules:
            self.solver.add_rule(function(*input_variables, value), And(*premise))

        self.variables += input_copied_variables + output_copied_variables
        self.function_args[identifier] = input_variables + [output_variable]

        return function

    def convert_term(self, term):
        match_symbol = str(term.decl())
        args = self.rule_args[match_symbol]
        semantic_term = self.rule_term[match_symbol]

        current_cxt = self.cxt_variables.copy()

        for i, symbol in enumerate(args):
            self.cxt_variables[symbol] = self.convert_term(term.arg(i))

        converted = semantic_term.accept(self)[0][1]

        self.cxt_variables = current_cxt

        return converted