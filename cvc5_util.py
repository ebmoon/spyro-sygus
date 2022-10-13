from cvc5 import Kind
from collections import defaultdict
from spyro_ast import ASTVisitor
from abc import ABC

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

class SynthesisOracleInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        self.cxt_variables = {}
        self.cxt_functions = {}

        self.rule_dict = {}

        self.grammar = None

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

        current_cxt = self.cxt_variables.copy()
        self.cxt_variables = semantic_rule.match.accept(self)

        term = semantic_rule.term.accept(self)
        self.grammar.add_rule(self.cxt_variables[symbol], term)

        self.cxt_variables = current_cxt

    def visit_production_match(self, production_match):
        head_symbol = production_match.identifier
        variables = production_match.variables
        sorts = self.rule_dict[head_symbol]

        context = self.cxt_variables.copy()
        for i, symbol in enumerate(variables):
            match_arg_symbol = sorts[i]
            context[symbol] = self.cxt_variables[match_arg_symbol]
        
        return context

    def visit_declare_language_command(self, declare_language_command):
        nonterminals = declare_language_command.nonterminals
        syntactic_rules = declare_language_command.syntactic_rules

        fun_variables = self.cxt_variables.values()
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

        for identifier, sort in inputs:
            arg_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt_variables[identifier] = arg_var

        out_var = self.solver.mkVar(output_sort.accept(self), output_id)
        self.cxt_variables[output_id] = out_var

    def visit_program(self, program):
        for target_function in program.target_functions:
            target_function.accept(self)

        args = self.cxt_variables.values()
        bool_sort = self.solver.getBooleanSort()
        
        target_function.lang_syntax.accept(self)
        target_function.lang_semantics.accept(self)

        spec = self.solver.synthFun("spec", args, bool_sort, self.grammar)

        return spec

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