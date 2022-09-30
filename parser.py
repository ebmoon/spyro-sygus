import ply.yacc

from lexer import SpyroSygusLexer

class SpyroSygusParser(object):
    tokens = SpyroSygusLexer.tokens

    def p_program(self, p):
        """program : set_logic_command variable_plus relation_plus generator function_plus"""
        
        p[0] = Program(p[1], p[2], p[3], p[4], p[5])
        self._ast_root = p[0]

    def p_set_logic_command(self, p):
        """set_logic_command : TK_LPAREN TK_SET_LOGIC TK_SYMBOL TK_RPAREN"""
        
        p[0] = SetLogicCommand(p[3])

    def p_variable_plus(self, p):
        """variable_plus : variable_plus variable
                         | variable"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]

    def p_variable(self, p):
        """variable : TK_LPAREN TK_DEFINE_VARIABLE symbol sort term TK_RPAREN"""
        p[0] = DefineVariableCommand(p[3], p[4], p[5])

    def p_sort(self, p):
        """sort : TK_SYMBOL"""
        p[0] = p[1]

    def p_term_star(self, p):
        """term_star : term_plus
                     | """
        if 2 == len(p):
            p[0] = p[1]
        else:
            p[0] = []

    def p_term_plus(self, p):
        """term_plus : term_plus term
                     | term"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]] 

    def p_symbol(self, p):
        """symbol : TK_SYMBOL"""
        p[0] = IdentifierTerm(p[1])

    def p_numeral(self, p):
        """numeral : TK_NUMERAL"""
        p[0] = NumeralTerm(p[1])

    def p_constant(self, p):
        """constant : TK_LPAREN TK_CONSTANT sort TK_RPAREN"""
        p[0] = ConstantTerm(p[3])

    def p_app(self, p):
        """app : TK_LPAREN symbol term_star TK_RPAREN"""
        p[0] = FunctionApplicationTerm(p[2], p[3])

    def p_term(self, p):
        """term : symbol
                | numeral
                | app
                | constant"""
        p[0] = p[1]       
    
    def p_relation_plus(self, p):
        """relation_plus : relation_plus relation
                         | relation"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]
    
    def p_relation(self, p):
        """relation : TK_LPAREN TK_DEFINE_RELATION term TK_RPAREN"""
        p[0] = DefineRelationCommand(p[3])

    def p_generator(self, p):
        """generator : TK_LPAREN TK_DEFINE_GENERATOR TK_LPAREN rule_plus TK_RPAREN TK_RPAREN"""
        p[0] = DefineGeneratorCommand(p[4])
    
    def p_rule_plus(self, p):
        """rule_plus : rule_plus rule
                     | rule"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]

    def p_rule(self, p):
        """rule : TK_LPAREN symbol sort TK_LPAREN term_plus TK_RPAREN TK_RPAREN"""
        p[0] = [p[2], p[3], p[5]]

    def p_function_plus(self, p):
        """function_plus : function_plus function
                         | function"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]

    def p_function(self, p):
        """function : TK_LPAREN TK_DEFINE_FUN symbol TK_LPAREN arg_plus TK_RPAREN sort term_plus TK_RPAREN"""
        p[0] = DefineFunctionCommand(p[3], p[5], p[7], p[8])
    
    def p_arg_plus(self, p):
        """arg_plus : arg_plus arg
                    | arg"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]        

    def p_arg(self, p):
        """arg : TK_LPAREN symbol sort TK_RPAREN"""
        p[0] = [p[2], p[3]]

    def p_error(self, p):
        if p:
            print("Parsing error at '%s'" % p.value)
        else:
            print("Parsing error at EOF")

    def __init__(self):
        self.parser = ply.yacc.yacc(debug=False, module=self, start="program")
        self.input_string = None
        self.lexer = None
        self._ast_root = None
    
    def _parse(self, reset: bool = True):
        self.parser.parse(self.input_string, lexer=self.lexer.lexer)
        if not reset:
            return self._ast_root
        self.input_string = None
        result = self._ast_root
        self._ast_root = None
        return result

    def parse(self, input_string):
        self.input_string = input_string
        self.lexer = SpyroSygusLexer()
        return self._parse()

