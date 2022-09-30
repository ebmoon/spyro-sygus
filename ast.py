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

    def __init__(self, id):
        self.id = id

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_sort_expression(self)

    def __eq__(self, other):
        if other is None:
            return False
        if not isinstance(other, SortExpression):
            return False
        return (self.id == other.id)

class Term(AST, ABC):
    
    def __init__(self):
        pass

class IdentifierTerm(Term):

    def __init__(self, id):
        super().__init__()
        self.id = id

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_identifier_term(self)

class NumeralTerm(Term):

    def __init__(self, value):
        super().__init__()
        self.value = value

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_numeral_term(self)


class FunctionApplicationTerm(Term):

    def __init__(self, id, args):
        super().__init__()
        self.id = id
        self.args = args

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_function_application_term(self)

class ConstantTerm(Term):

    def __init__(self, sort):
        super().__init__()
        self.sort = sort

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_constant_term(self)


class ProductionRule(AST):

    def __init__(self, head_symbol, sort, terms):
        self.head_symbol = head_symbol
        self.sort = sort
        self.terms = terms

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_production_rule(self)


class Grammar(AST):

    def __init__(self, nonterminals, rule_lists):
        self.nonterminals = nonterminals
        self.rules = {}

        for rule in rule_lists:
            rules[rule.head_symbol] = rule

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_grammar(self)


@unique
class CommandKind(Enum):
    SET_LOGIC = auto()
    DEFINE_VAR = auto()
    DEFINE_REL = auto()
    DEFINE_GENERATOR = auto()
    DEFINE_FUN = auto()

class Command(AST, ABC):
    
    def __init__(self, command_kind: CommandKind):
        self.command_kind: = command_kind

class SetLogicCommand(Command):

    def __init__(self, logic):
        super().__init__(CommandKind.SET_LOGIC)
        self.logic = logic

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_set_logic_command(self)

class DefineVariableCommand(Command):

    def __init__(self, id, sort, grammar):
        super().__init__(CommandKind.DEFINE_VAR)
        self.id = id
        self.sort = sort
        self.term = Grammar

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_variable_command(self)

class DefineRelationCommand(Command):

    def __init__(self, term):
        super().__init__(CommandKind.DEFINE_REL)
        self.term = term

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_relation_command(self)

class DefineGeneratorCommand(Command):

    def __init__(self, grammar):
        super().__init__(CommandKind.DEFINE_GENERATOR)
        self.grammar = grammar

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_generator_command(self)

class DefineFunctionCommand(Command):

    def __init__(self, id, args, sort, term):
        super().__init__(CommandKind.DEFINE_FUN)
        self.id = id
        self.args = args
        self.sort = sort
        self.term = term

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_define_function_command(self)

class Program(AST):
    def __init__(self,
            set_logic_command,
            define_variable_commands,
            define_relation_commands,
            generator,
            define_function_commands
        )
        
        self.set_logic_command = set_logic_command
        self.define_variable_commands = define_variable_commands
        self.define_relation_commands = define_relation_commands
        self.generator = generator
        self.define_function_commands = define_function_commands

    def accept(self, visitor: ASTVisitor):
        return visitor.visit_program(self)