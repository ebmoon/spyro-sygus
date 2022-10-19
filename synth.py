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

            if not self.added_const_grammar:
                self.solver.setOption("sygus-grammar-cons", "any-const")
                self.added_const_grammar = True

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

        for identifier, sort in inputs:
            arg_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt_variables[identifier] = arg_var

        out_var = self.solver.mkVar(output_sort.accept(self), output_id)
        self.cxt_variables[output_id] = out_var

    def visit_program(self, program):
        for target_function in program.target_functions:
            target_function.accept(self)

        args = list(self.cxt_variables.values())
        bool_sort = self.solver.getBooleanSort()
        
        program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        spec = self.solver.synthFun("spec", args, bool_sort, self.grammar)

        return spec

class SynthesisUnrealizabilityChecker(BaseUnrealizabilityChecker):

    def __init__(self, solver, pos, neg):
        super().__init__(solver, pos, neg)

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
        self.cxt_functions[identifier] = function
        self.function_args[identifier] = input_variables + [output_variable]

        return function

    def visit_program(self, program):
        [target_function.accept(self) for target_function in program.target_functions]
        sem_functions = program.lang_syntax.accept(self)
        program.lang_semantics.accept(self)

        start_sem = sem_functions[0]
        realizable = Function("realizable", BoolSort())

        head = realizable()
        
        body_arg = [item for e_pos in self.pos for item in e_pos]
        body_arg += [item for e_neg in self.neg for item in e_neg]
        body_arg += [True] * len(self.pos)
        body_arg += [False] * len(self.neg)

        body = start_sem(*body_arg)

        self.solver.register_relation(realizable)
        self.solver.add_rule(head, body)

        return realizable

class SynthesisOracle(object):

    def __init__(self, ast):
        self.ast = ast

    def add_positive_example(self, synthesizer, spec, e):
        e = [convert_z3_to_cvc5(synthesizer, v) for v in e]
        term = synthesizer.mkTerm(Kind.APPLY_UF, spec, *e)
        
        synthesizer.addSygusConstraint(term)

    def add_negative_example(self, synthesizer, spec, e):
        e = [convert_z3_to_cvc5(synthesizer, v) for v in e]
        term = synthesizer.mkTerm(Kind.APPLY_UF, spec, *e)
        neg_term = synthesizer.mkTerm(Kind.NOT, term)
        
        synthesizer.addSygusConstraint(neg_term)

    def synthesize(self, pos, neg, check_realizable = True):   
        if check_realizable:
            solver = Fixedpoint()
            checker = SynthesisUnrealizabilityChecker(solver, pos, neg)
            realizable = self.ast.accept(checker)

        if not check_realizable or solver.query(realizable) == sat:
            synthesizer = cvc5.Solver()
            synthesizer.setOption("sygus", "true")
            synthesizer.setOption("incremental", "true")
            synthesizer.setLogic("LIA")   

            initializer = SynthesisOracleInitializer(synthesizer)
            spec = self.ast.accept(initializer)

            for e in pos:
                self.add_positive_example(synthesizer, spec, e)

            for e in neg:
                self.add_negative_example(synthesizer, spec, e)

            synthResult = synthesizer.checkSynth()
            if synthResult.hasSolution():
                return synthesizer.getSynthSolution(spec)
            else:
                # should not happen
                print(pos, neg)
                print(f"Unknown: {synthResult.isUnknown()}")
                raise NotImplementedError
        else:
            return None