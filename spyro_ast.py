from abc import ABC, abstractmethod
from enum import auto, Enum, unique

class ASTVisitor(object):

    @abstractmethod
    def visit_sort_expression(self, sort_expression):
        raise NotImplementedError

    @abstractmethod
    def visit_identifier_term(self, identifier_term):
        raise NotImplementedError

    @abstractmethod
    def visit_numeral_term(self, numeral_term):
        raise NotImplementedError

    @abstractmethod
    def visit_function_application_term(self, function_application_term):
        raise NotImplementedError

    @abstractmethod
    def visit_constant_term(self, constant_term):
        raise NotImplementedError

    @abstractmethod
    def visit_production_rule(self, production_rule):
        raise NotImplementedError

    @abstractmethod
    def visit_grammar(self, grammar):
        raise NotImplementedError

    @abstractmethod
    def visit_declare_language_command(self, declare_syntax_command):
        raise NotImplementedError

    @abstractmethod
    def visit_declare_semantics_command(self, declare_semantics_command):
        raise NotImplementedError

    @abstractmethod
    def visit_target_function_command(self, target_function_command):
        raise NotImplementedError

    @abstractmethod
    def visit_program(self, program):
        raise NotImplementedError

class AST(object):

    @abstractmethod
    def accept(self, visitor: ASTVisitor):
        raise NotImplementedError

class SortExpression(AST):

    def __init__(self, identifier):
        self.identifier = identifier

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_sort_expression(self)

    def __eq__(self, other):
        if other is None:
            return False
        if not isinstance(other, SortExpression):
            return False
        return (self.identifier == other.ididentifier)

    def __str__(self):
        return self.identifier

class Term(AST, ABC):
    
    def __init__(self):
        pass

class IdentifierTerm(Term):

    def __init__(self, identifier):
        super().__init__()
        self.identifier = identifier

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_identifier_term(self)

    def __str__(self):
        return self.identifier

class NumeralTerm(Term):

    def __init__(self, value):
        super().__init__()
        self.value = value

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_numeral_term(self)

    def __str__(self):
        return str(self.value)

class FunctionApplicationTerm(Term):

    def __init__(self, identifier, args):
        super().__init__()
        self.identifier = identifier
        self.args = args

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_function_application_term(self)

    def __str__(self):
        args_str = " ".join([str(arg) for arg in self.args])
        return f"({self.identifier} {args_str})"

class ProductionRule(AST):

    def __init__(self, head_symbol, sort, terms):
        self.head_symbol = head_symbol
        self.sort = sort
        self.terms = terms

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_production_rule(self)

    def __str__(self):
        terms_str = " ".join([str(term) for term in self.terms])
        return f"({self.head_symbol} {self.sort} ({terms_str}))"

class Grammar(AST):

    def __init__(self, nonterminals, rule_lists):
        self.nonterminals = nonterminals
        self.rules = {}

        for rule in rule_lists:
            self.rules[rule.head_symbol] = rule

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_grammar(self)

    def __str__(self):
        nonterminals_str = " ".join([f"({symbol} {sort})" for (symbol, sort) in self.nonterminals])
        rules_str = "\r\n".join([str(rule) for rule in self.rules.values()])
        
        return f"({nonterminals_str}) ({rules_str})"

@unique
class CommandKind(Enum):
    TARGET_FUN = auto()
    LANG_SYN = auto()
    LANG_SEM = auto()

class Command(AST, ABC):
    
    def __init__(self, command_kind: CommandKind):
        self.command_kind = command_kind

class DeclareLanguageCommand(Command):
    
    def __init__(self, nonterminals, rules):
        super().__init__(CommandKind.LANG_SYN)
        self.nonterminals = nonterminals
        self.syntactic_rules = rules

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_declare_language_command(self)

    def __str__(self):
        nons_str = " ".join([f"({symbol} {sort})" for (symbol, sort) in self.nonterminals])
        rules_str = "\r\n".join([str(rule) for rule in self.syntactic_rules])

        return f"(declare-language \r\n ({nons_str}) \r\n\r\n ({rules_str}))"

class DeclareSemanticsCommand(Command):

    def __init__(self, rules):
        super().__init__(CommandKind.LANG_SYN)
        self.semantic_rules = rules

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_declare_semantics_command(self)

    def __str__(self):
        rules_str = "\r\n".join([str(rule) for rule in self.semantic_rules])

        return f"(declare-semantics \r\n ({rules_str}) \r\n)"

class TargetFunctionCommand(Command):

    def __init__(self, identifier, inputs, output, term):
        super().__init__(CommandKind.TARGET_FUN)
        self.identifier = identifier
        self.inputs = inputs
        self.output = output
        self.term = term

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_target_function_command(self)

    def __str__(self):
        inputs_str = " ".join([f"({symbol} {sort})" for (symbol, sort) in self.inputs])
        out_id, out_sort = self.output
        return f"(target-fun {self.identifier} ({inputs_str}) ({out_id} {out_sort}) {self.term})"

class Program(AST):
    def __init__(self, target_functions, lang_syntax, lang_semantics):
        
        self.target_functions = target_functions
        self.lang_syntax = lang_syntax
        self.lang_semantics = lang_semantics

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_program(self)

    def __str__(self):
        s + "\r\n".join([str(cmd) for cmd in self.target_functions]) + "\r\n\r\n"
        s += str(self.lang_syntax) + "\r\n\r\n"
        s += str(self.lang_semantics) 

        return s