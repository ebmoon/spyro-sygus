from z3 import *
from abc import ABC
from z3_util import *
import cvc5
from cvc5 import Kind

class BaseUnrealizabilityChecker(ASTVisitor, ABC):
    
    def __init__(self, solver, pos, neg):
        self.solver = solver
        self.pos = pos
        self.neg = neg

        self.cxt_sorts = reserved_sorts.copy()
        self.cxt_nonterminals = {}
        self.cxt_variables = {}
        self.cxt_functions = {}
        
        self.current_nonterminal = None
        self.rule_dict = {}
        self.rule_args = {}
        self.rule_term = {}
        self.function_args = {}

        self.num_examples = len(pos) + len(neg)
        self.var_copies = {}

        self.function_variables_save = None
        self.copied_function_variables_save = None

        self.var_cnt = 0

    def fresh_var(self, id, sort):
        if type(sort) == SortExpression:
            sort = sort.accept(self)
        
        var, _ = self.define_new_variable(f'{id}_{self.var_cnt}', sort)        
        self.var_cnt += 1

        return var

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
            fn, sort = self.cxt_functions[function_application_term.identifier]
            out_var = self.fresh_var(fn.name(), sort)
            return [(premise + [fn(*args, out_var, True)], out_var) for premise, args in args_join]

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
            
            for symbol in self.var_copies:
                self.cxt_variables[symbol] = self.var_copies[symbol][n]

            premise, term = semantic_rule.term.accept(self)[0]
            terms.append(term)

            self.cxt_variables = current_cxt_variables


        head = sem_function(*self.copied_function_variables(), *terms)

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
        ret_variable_copies = {symbol:[] for symbol in variables}

        for n in range(self.num_examples):
            current_cxt = self.cxt_variables.copy()

            for i, symbol in enumerate(variables):
                term_sort = sorts[i]

                var_symbol = symbol if term_sort.identifier in self.cxt_sorts else f'{symbol}_{n}'
                ret_variable, _ = self.define_new_variable(var_symbol, term_sort)
                ret_variable_copies[symbol].append(ret_variable)

            self.cxt_variables = current_cxt

        for i, symbol in enumerate(variables):
            term_sort = sorts[i]
            ret_variables = ret_variable_copies[symbol]
            if str(term_sort) in self.cxt_nonterminals:
                ret_sort, sem_function = self.cxt_nonterminals[str(term_sort)]
                body.append(sem_function(*self.copied_function_variables(), *ret_variables))

        return (head_symbol, body, variables, ret_variable_copies)

    def visit_declare_language_command(self, declare_language_command):
        nonterminals = declare_language_command.nonterminals
        syntactic_rules = declare_language_command.syntactic_rules
           
        for syntactic_rule in syntactic_rules:
            syntactic_rule.accept(self)

        var_sorts = [variable.sort() for variable in self.copied_function_variables()]
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
        output_id, output_sort_str = target_function_command.output
        term = target_function_command.term

        input_sorts = []
        input_variables = []
        copied_variables = []
        for input_id, input_sort in inputs:
            variable, sort = self.define_new_variable(input_id, input_sort)
            input_sorts.append(sort)
            input_variables.append(variable)
            self.var_copies[input_id] = []

        output_variable, output_sort = self.define_new_variable(output_id, output_sort_str)
        self.var_copies[output_id] = []


        for i in range(self.num_examples):
            for input_id, input_sort in inputs:
                variable, _ = self.define_new_variable(f'{input_id}_{i}', input_sort)
                copied_variables.append(variable)
                self.var_copies[input_id].append(variable)

            variable, _ = self.define_new_variable(f'{output_id}_{i}', output_sort_str)
            copied_variables.append(variable)
            self.var_copies[output_id].append(variable)

        function = Function(identifier, *input_sorts, output_sort, BoolSort(), BoolSort())
        self.cxt_functions[identifier] = (function, output_sort)
        self.solver.register_relation(function)

        rules = term.accept(self)
        for premise, value in rules:
            self.solver.add_rule(function(*input_variables, output_variable, output_variable == value), And(*premise))

        self.function_args[identifier] = input_variables + [output_variable]

        return function

    def function_variables(self):
        if self.function_variables_save is not None:
            return self.function_variables_save
        else:
            self.function_variables_save = [
                variable for _, var_list in self.function_args.items() 
                         for variable in var_list]
            return self.function_variables_save

    def copied_function_variables(self):
        if self.copied_function_variables_save is not None:
            return self.copied_function_variables_save
        else:
            fun_variables = self.function_variables()
            copied_variables = []
            for i in range(self.num_examples):
                for v in fun_variables:
                    symbol = v.decl().name()
                    copied_variables.append(self.var_copies[symbol][i])
            
            self.copied_function_variables_save = copied_variables
            return self.copied_function_variables_save

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

    def convert_term(self, term):
        if term.getKind() == Kind.LAMBDA:
            return self.convert_term(term[1])
        elif term.getKind() == Kind.LT:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 < t2
        elif term.getKind() == Kind.LEQ:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 <= t2
        elif term.getKind() == Kind.GT:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 > t2
        elif term.getKind() == Kind.GEQ:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 >= t2
        elif term.getKind() == Kind.EQUAL:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 == t2
        elif term.getKind() == Kind.DISTINCT:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 != t2
        elif term.getKind() == Kind.ADD:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 + t2
        elif term.getKind() == Kind.MULT:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 * t2
        elif term.getKind() == Kind.SUB:
            t1 = self.convert_term(term[0])
            t2 = self.convert_term(term[1])
            return t1 - t2
        elif term.getKind() == Kind.NOT:
            t1 = self.convert_term(term[0])
            return Not(t1)
        elif term.getKind() == Kind.OR:
            args = [self.convert_term(term[i]) for i in range(term.getNumChildren())]
            return Or(*args)
        elif term.getKind() == Kind.AND:
            args = [self.convert_term(term[i]) for i in range(term.getNumChildren())]
            return And(*args)
        elif term.getKind() == Kind.NEG:
            t1 = self.convert_term(term[0])
            return - t1        
        elif term.getKind() == Kind.CONST_BOOLEAN:
            return term.getBooleanValue()
        elif term.getKind() == Kind.CONST_INTEGER:
            return term.getIntegerValue()
        elif term.getKind() == Kind.VARIABLE:
            return self.cxt_variables[term.getSymbol()]
        else:
            print(term, term.getKind())
            raise NotImplementedError