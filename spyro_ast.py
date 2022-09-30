from abc import ABC, abstractmethod
from enum import auto, Enum, unique

class ASTVisitor(object):

    @abstractmethod
    def visit_sort_expresion(self, sort_expression):
        raise NotImplementedError

    @abstractmethod
    def visit_identifier_term(self, identifier_term):
        raise NotImplementedError

    @abstractmethod
    def visit_numeral_term(self, numeral_term):
        raise NotImplementedError

    @abstractmethod
    def visit_function_application_term(self, function_appliation_term):
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
    def visit_set_logic_command(self, set_logic_command):
        raise NotImplementedError

    @abstractmethod
    def visit_define_variable_command(self, define_variable_command):
        raise NotImplementedError

    @abstractmethod
    def visit_define_relation_command(self, define_relation_command):
        raise NotImplementedError

    @abstractmethod
    def visit_define_generator_command(self, define_generator_command):
        raise NotImplementedError

    @abstractmethod
    def visit_define_function_command(self, define_function_command):
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

class ConstantTerm(Term):

    def __init__(self, sort):
        super().__init__()
        self.sort = sort

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_constant_term(self)

    def __str__(self):
        return f"(Constant {self.sort})"

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
    SET_LOGIC = auto()
    DEFINE_VAR = auto()
    DEFINE_REL = auto()
    DEFINE_GENERATOR = auto()
    DEFINE_FUN = auto()

class Command(AST, ABC):
    
    def __init__(self, command_kind: CommandKind):
        self.command_kind = command_kind

class SetLogicCommand(Command):

    def __init__(self, logic):
        super().__init__(CommandKind.SET_LOGIC)
        self.logic = logic

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_set_logic_command(self)

    def __str__(self):
        return f"(set-logic {self.logic})"

class DefineVariableCommand(Command):

    def __init__(self, identifier, sort, grammar):
        super().__init__(CommandKind.DEFINE_VAR)
        self.identifier = identifier
        self.sort = sort
        self.grammar = grammar

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_variable_command(self)

    def __str__(self):
        return f"(define-var {self.identifier} {self.sort} {self.grammar})"

class DefineRelationCommand(Command):

    def __init__(self, term):
        super().__init__(CommandKind.DEFINE_REL)
        self.term = term

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_relation_command(self)

    def __str__(self):
        return f"(define-rel {str(self.term)})"

class DefineGeneratorCommand(Command):

    def __init__(self, grammar):
        super().__init__(CommandKind.DEFINE_GENERATOR)
        self.grammar = grammar

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_generator_command(self)

    def __str__(self):
        return f"(generator {self.grammar})"

class DefineFunctionCommand(Command):

    def __init__(self, identifier, args, sort, term):
        super().__init__(CommandKind.DEFINE_FUN)
        self.identifier = identifier
        self.args = args
        self.sort = sort
        self.term = term

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_function_command(self)

    def __str__(self):
        args_str = " ".join([f"({symbol} {sort})" for (symbol, sort) in self.args])
        return f"(define-fun {self.identifier} ({args_str}) {self.sort} {self.term})"

class Program(AST):
    def __init__(self,
            set_logic_command,
            define_variable_commands,
            define_relation_commands,
            generator,
            define_function_commands):
        
        self.set_logic_command = set_logic_command
        self.define_variable_commands = define_variable_commands
        self.define_relation_commands = define_relation_commands
        self.generator = generator
        self.define_function_commands = define_function_commands

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_program(self)

    def __str__(self):
        s = f"{self.set_logic_command}" + "\r\n\r\n"
        s += "\r\n".join([str(cmd) for cmd in self.define_variable_commands]) + "\r\n\r\n"
        s += "\r\n".join([str(cmd) for cmd in self.define_relation_commands]) + "\r\n\r\n"
        s += str(self.generator) + "\r\n\r\n"
        s += "\r\n".join([str(cmd) for cmd in self.define_function_commands])

        return s