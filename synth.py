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

    def visit_program(self, program):
        for target_function in program.target_functions:
            target_function.accept(self)

        args = list(self.cxt_variables.values())
        bool_sort = self.solver.getBooleanSort()
        
        program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        spec = self.solver.synthFun("spec", args, bool_sort, self.grammar)

        return spec

class SynthesisOracle(object):

    def __init__(self, ast):
        self.synthesizer = cvc5.Solver()
        self.ast = ast

        self.synthesizer.setOption("sygus", "true")
        self.synthesizer.setOption("incremental", "true")
        self.synthesizer.setLogic("LIA")

        initializer = SynthesisOracleInitializer(self.synthesizer)
        self.spec = ast.accept(initializer)

        self.synthesizer.push(2)

        self.new_pos = []
        self.neg_may = []

    def add_positive_example(self, e):
        self.synthesizer.pop()
        e = [convert_z3_to_cvc5(self.synthesizer, v) for v in e]
        term = self.synthesizer.mkTerm(Kind.APPLY_UF, self.spec, *e)
        
        self.synthesizer.addSygusConstraint(term)
        self.new_pos.append(term)

        self.synthesizer.push()

        for e_term in self.neg_may:
            self.synthesizer.addSygusConstraint(e_term)

    def add_negative_example(self, e):
        e = [convert_z3_to_cvc5(self.synthesizer, v) for v in e]
        term = self.synthesizer.mkTerm(Kind.APPLY_UF, self.spec, *e)
        neg_term = self.synthesizer.mkTerm(Kind.NOT, term)
        
        self.synthesizer.addSygusConstraint(neg_term)
        self.neg_may.append(neg_term)

    def freeze_negative_example(self):
        self.synthesizer.pop()

        for e_term in self.neg_may:
            self.synthesizer.addSygusConstraint(e_term)
        
        self.neg_may = []

        self.synthesizer.push()

    def clear_negative_may(self):
        self.synthesizer.pop()     
        
        self.neg_may = []

        self.synthesizer.push()

    def clear_negative_example(self):
        self.synthesizer.pop(2)

        for e_term in self.new_pos:
            self.synthesizer.addSygusConstraint(e_term)
        
        self.new_pos = []
        self.neg_may = []

        self.synthesizer.push(2)

    def synthesize(self, pos, neg, check_realizable = True):   
        if check_realizable:
            solver = Fixedpoint()
            checker = SynthesisUnrealizabilityChecker(solver, pos, neg)
            realizable = self.ast.accept(checker)

        if not check_realizable or solver.query(realizable) == sat:
            synthResult = self.synthesizer.checkSynth()
            if synthResult.hasSolution():
                return self.synthesizer.getSynthSolution(self.spec)
            else:
                # should not happen
                print(pos, neg)
                print(f"Unknown: {synthResult.isUnknown()}")
                raise NotImplementedError
        else:
            return None