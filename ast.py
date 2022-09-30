from abc import ABC, abstractmethod
from enum import auto, Enum, unique

class ASTVisitor(object):

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


class Term(AST, ABC):


class IdentifierTerm(Term):

class NumeralTerm(Term):

class FunctionApplicationTerm(Term):

class ConstantTerm(Term):

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

    def __init__(self, id, sort, term):
        super().__init__(CommandKind.DEFINE_VAR)
        self.id = id
        self.sort = sort
        self.term = term

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