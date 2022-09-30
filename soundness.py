import cvc5
from spyro_ast import *
from cvc5 import Kind
from cvc5_util import *

class SoundnessOracleInitializer(ASTVisitor):
    
    def __init__(self, solver):
        self.solver = solver
        self.cxt = {}
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
        return self.cxt[identifier_term.identifier]

    def visit_numeral_term(self, numeral_term):
        return self.solver.mkInteger(numeral_term.value)

    def visit_function_application_term(self, function_application_term):
        kind = kind_dict[function_application_term.identifier]
        arg_terms = [arg.accept(self) for arg in function_application_term.args]
        if function_application_term.identifier in reserved:
            return self.solver.mkTerm(kind, *arg_terms)
        else:
            return self.solver.mkTerm(kind, self.cxt[function_application_term.identifier], *arg_terms)

    def visit_constant_term(self, constant_term):
        self.current_grammar.addAnyConstant(self.current_head_symbol)

    def visit_production_rule(self, production_rule):
        head_symbol_term = self.cxt[production_rule.head_symbol]
        self.current_head_symbol = head_symbol_term

        rule_terms = [rule.accept(self) for rule in production_rule.terms]
        rule_terms = [terms for term in rule_terms if term != None]

        self.current_head_symbol = None        

        return rule_terms

    def visit_grammar(self, grammar):
        current_cxt = self.cxt.copy()

        nonterminal_vars = []
        for identifier, sort in grammar.nonterminals:
            nonterminal_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt[identifier] = nonterminal_var
            nonterminal_vars.append(nonterminal_var)

        g = self.solver.mkGrammar(current_cxt.values(), nonterminal_vars)
        self.current_grammar = g

        for head_symbol, rule in grammar.rules.items():
            g.addRules(self.cxt[head_symbol], rule.accept(self))

        self.current_grammar = None
        self.cxt = current_cxt

        return g

    def visit_set_logic_command(self, set_logic_command):
        self.solver.setLogic(set_logic_command.logic)

    def visit_define_variable_command(self, define_variable_command):
        sort = define_variable_command.sort.accept(self)

        current_cxt = self.cxt
        self.cxt = {}

        g = define_variable_command.grammar.accept(self)
        term = self.solver.synthFun(define_variable_command.identifier, [], sort, g)

        self.cxt = current_cxt        
        self.cxt[define_variable_command.identifier] = term

        return term

    def visit_define_constraint_command(self, define_constraint_command):
        self.solver.addSygusConstraint(define_constraint_command.term.accept(self))

    def visit_define_generator_command(self, define_generator_command):
        raise NotImplementedError

    def visit_define_function_command(self, define_function_command):
        current_cxt = self.cxt.copy()

        args = []
        for identifier, sort in define_function_command.args:
            arg_var = self.solver.mkVar(sort.accept(self), identifier)
            self.cxt[identifier] = arg_var
            args.append(arg_var)
        
        sort = define_function_command.sort.accept(self)
        term = define_function_command.term.accept(self)

        f = self.solver.defineFun(define_function_command.identifier, args, sort, term)

        self.cxt = current_cxt
        self.cxt[define_function_command.identifier] = f

        return f

    def visit_program(self, program):
        # Set logic of the solver
        program.set_logic_command.accept(self)
        variables = [cmd.accept(self) for cmd in program.define_variable_commands]
        functions = [cmd.accept(self) for cmd in program.define_function_commands]
        constraints = [cmd.accept(self) for cmd in program.define_constraint_commands]

        return (self.cxt, variables, constraints, functions)

class SoundnessOracle(object):
    def __init__(self, ast):
        self.solver = cvc5.Solver()
        self.ast = ast
        self.__initializer = SoundnessOracleInitializer(self.solver)

        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        self.solver.setOption("sygus-grammar-cons", "any-const")
        
        cxt, variables, constraints, functions = ast.accept(self.__initializer)
        self.cxt = cxt
        self.variables = variables
        self.constraints = constraints
        self.functions = functions

    # Input : Candadate specification as CVC5 term
    # Output : Counterexample as CVC5 term
    def check_soundness(self, spec):
        self.solver.push()

        spec_neg = self.solver.mkTerm(Kind.NOT, spec)
        self.solver.addSygusConstraint(spec_neg)

        if self.solver.checkSynth().hasSolution():
            return self.solver.getSynthSolutions(self.variables)
        else:
            return None

        self.solver.pop()
        

