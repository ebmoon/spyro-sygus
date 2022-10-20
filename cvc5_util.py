from cvc5 import Kind
from spyro_ast import *
from collections import defaultdict

TIMEOUT = str(300000)

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

class BaseInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        self.cxt_variables = {}
        self.cxt_functions = {}

        self.rule_dict = {}

        self.grammar = None
        self.added_const_grammar = False

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
            return self.solver.mkTerm(Kind.NEG, arg_terms[0])
        elif function_application_term.identifier in reserved_functions:
            return self.solver.mkTerm(kind, *arg_terms)
        else:
            return self.solver.mkTerm(kind, self.cxt_functions[function_application_term.identifier], *arg_terms)

    def visit_syntactic_rule(self, syntactic_rule):
        for prod in syntactic_rule.productions:
            prod.accept(self) 

    def visit_production_rule(self, production_rule):
        head_symbol = production_rule.head_symbol
        sorts = production_rule.sorts

        self.rule_dict[head_symbol] = sorts

    def visit_semantic_rule(self, semantic_rule):
        symbol = semantic_rule.nonterminal
        nonterminal = self.cxt_variables[symbol]

        current_cxt = self.cxt_variables.copy()

        try:
            self.cxt_variables = semantic_rule.match.accept(self)

            term = semantic_rule.term.accept(self)
            self.grammar.addRule(nonterminal, term)
        except ConstantGrammarException:
            self.grammar.addAnyConstant(nonterminal)

        self.cxt_variables = current_cxt

    def visit_production_match(self, production_match):
        head_symbol = production_match.identifier
        variables = production_match.variables
        sorts = self.rule_dict[head_symbol]

        context = self.cxt_variables.copy()
        for i, symbol in enumerate(variables):
            match_arg_symbol = sorts[i].identifier
            if match_arg_symbol in self.cxt_variables:
                context[symbol] = self.cxt_variables[match_arg_symbol]
            else:
                raise ConstantGrammarException
        
        return context

    def visit_declare_language_command(self, declare_language_command):
        nonterminals = declare_language_command.nonterminals
        syntactic_rules = declare_language_command.syntactic_rules

        fun_variables = list(self.cxt_variables.values())
        nonterminal_vars = []

        for i, syntactic_rule in enumerate(syntactic_rules):
            symbol, sort = nonterminals[i]
            sort = sort.accept(self)

            nonterminal_var = self.solver.mkVar(sort, symbol)
            self.cxt_variables[symbol] = nonterminal_var
            nonterminal_vars.append(nonterminal_var)
            
            syntactic_rule.accept(self)

        self.grammar = self.solver.mkGrammar(fun_variables, nonterminal_vars)

    def visit_declare_semantics_command(self, declare_semantics_command):
        for rule in declare_semantics_command.semantic_rules:
            rule.accept(self)

    def visit_target_function_command(self, target_function_command):
        inputs = target_function_command.inputs
        output_id, output_sort = target_function_command.output

        arg_vars = []
        for identifier, sort in inputs:
            arg_var = self.solver.mkVar(sort.accept(self), identifier)
            arg_vars.append(arg_var)
            self.cxt_variables[identifier] = arg_var

        out_sort = output_sort.accept(self)
        out_var = self.solver.mkVar(out_sort, output_id)
        self.cxt_variables[output_id] = out_var

        term = target_function_command.term.accept(self)
        f = self.solver.defineFun(target_function_command.identifier, arg_vars, out_sort, term)

        return (f, arg_vars, out_var)