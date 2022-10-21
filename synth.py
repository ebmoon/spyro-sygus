from z3 import *
from spyro_ast import *
from z3_util import *
from unrealizable import *
from cvc5_util import *
from abc import ABC
import cvc5

class ConstantGrammarException(Exception):
    pass

class SynthesisOracleInitializer(ASTVisitor, ABC):
    
    def __init__(self, solver):
        self.solver = solver
        self.cxt_variables = {}
        self.cxt_functions = {}

        self.rule_dict = {}

        self.sygus_vars = []

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
        sygus_arg_vars = []
        for identifier, sort in inputs:
            sort = sort.accept(self)
            arg_var = self.solver.mkVar(sort, identifier)
            sygus_var = self.solver.declareSygusVar(identifier, sort)
            
            arg_vars.append(arg_var)
            sygus_arg_vars.append(sygus_var)
            self.sygus_vars.append(sygus_var)
            
            self.cxt_variables[identifier] = arg_var

        out_sort = output_sort.accept(self)
        out_var = self.solver.mkVar(out_sort, output_id)
        sygus_out_var = self.solver.declareSygusVar(output_id, out_sort)
        self.cxt_variables[output_id] = out_var

        self.sygus_vars.append(sygus_out_var)

        term = target_function_command.term.accept(self)
        f = self.solver.defineFun(target_function_command.identifier, arg_vars, out_sort, term)

        return (f, sygus_arg_vars, sygus_out_var)

    def visit_program(self, program):
        funs = [target_fun.accept(self) for target_fun in program.target_functions]
        
        args = list(self.cxt_variables.values())
        bool_sort = self.solver.getBooleanSort()

        program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        body = []
        for f, arg_vars, out_var in funs:
            fun_app = self.solver.mkTerm(Kind.APPLY_UF, f, *arg_vars)
            t = self.solver.mkTerm(Kind.EQUAL, out_var, fun_app)
            body.append(t)

        body_conj = self.solver.mkTerm(Kind.AND, *body) if len(body) > 1 else \
            body[0] if len(body) > 0 else self.solver.mkTrue()

        spec = self.solver.synthFun("spec", args, bool_sort, self.grammar)
        head = self.solver.mkTerm(Kind.APPLY_UF, spec, *self.sygus_vars)

        soundness_constraint = self.solver.mkTerm(Kind.IMPLIES, body_conj, head)
        self.solver.addSygusConstraint(soundness_constraint)

        return spec, self.sygus_vars, args

class SynthesisOracle(object):

    def __init__(self, ast):
        self.synthesizer = cvc5.Solver()
        self.ast = ast

        self.synthesizer.setOption("sygus", "true")
        self.synthesizer.setOption("incremental", "true")
        self.synthesizer.setLogic("LIA")

        initializer = SynthesisOracleInitializer(self.synthesizer)
        self.spec, self.sygus_vars, self.vars = ast.accept(initializer)
        self.var_list = self.synthesizer.mkTerm(Kind.VARIABLE_LIST, *self.vars)

    def synthesize_sound(self):
        synthResult = self.synthesizer.checkSynth()
        if synthResult.hasSolution():
            return self.synthesizer.getSynthSolution(self.spec)
        else:
            return None

    def synthesize_stronger(self, phi_list, phi):   
        self.synthesizer.push(1)

        phi_sygus_app = self.synthesizer.mkTerm(Kind.APPLY_UF, phi, *self.sygus_vars)
        spec_sygus_app = self.synthesizer.mkTerm(Kind.APPLY_UF, self.spec, *self.sygus_vars)
        strengthening_constraint = self.synthesizer.mkTerm(Kind.IMPLIES, spec_sygus_app, phi_sygus_app)

        self.synthesizer.addSygusConstraint(strengthening_constraint)

        phi_list_app = [self.synthesizer.mkTerm(Kind.APPLY_UF, p, *self.vars) for p in phi_list]
        phi_app = self.synthesizer.mkTerm(Kind.APPLY_UF, phi, *self.vars)
        spec_app = self.synthesizer.mkTerm(Kind.APPLY_UF, self.spec, *self.vars)
        spec_app_neg = self.synthesizer.mkTerm(Kind.NOT, spec_app)
        strengthening_witness = self.synthesizer.mkTerm(Kind.AND, spec_app_neg, phi_app, *phi_list_app)
        strict_constraint = self.synthesizer.mkTerm(Kind.EXISTS, self.var_list, strengthening_witness)

        self.synthesizer.addSygusConstraint(strict_constraint)

        synthResult = self.synthesizer.checkSynth()
        if synthResult.hasSolution():
            soln = self.synthesizer.getSynthSolution(self.spec)
            self.synthesizer.pop(1)
            return soln
        else:
            self.synthesizer.pop(1)
            return None