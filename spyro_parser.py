import ply.yacc

from spyro_lexer import SpyroSygusLexer
from spyro_ast import *

class SpyroSygusParser(object):
    tokens = SpyroSygusLexer.tokens

    def p_program(self, p):
        """program : target_fun_plus declare_language declare_semantics"""
        
        p[0] = Program(p[1], p[2], p[3])
        self._ast_root = p[0]

    def p_target_fun_plus(self, p):
        """target_fun_plus : target_fun_plus target_fun
                           | target_fun"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]        

    def p_target_fun(self, p):
        """target_fun : TK_LPAREN TK_TARGET_FUN TK_SYMBOL TK_LPAREN arg_plus TK_RPAREN arg term TK_RPAREN"""
        p[0] = TargetFunctionCommand(p[3], p[5], p[7], p[8])

    def p_arg_plus(self, p):
        """arg_plus : arg_plus arg
                    | arg"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]        

    def p_arg(self, p):
        """arg : TK_LPAREN TK_SYMBOL sort TK_RPAREN"""
        p[0] = (p[2], p[3])

    def p_sort_star(self, p):
        """sort_star : sort_plus
                     | """
        if 2 == len(p):
            p[0] = p[1]
        else:
            p[0] = []

    def p_sort_plus(self, p):
        """sort_plus : sort_plus sort
                     | sort"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]    

    def p_sort(self, p):
        """sort : TK_SYMBOL"""
        p[0] = SortExpression(p[1])

    def p_symbol(self, p):
        """symbol : TK_SYMBOL"""
        p[0] = IdentifierTerm(p[1])

    def p_numeral(self, p):
        """numeral : TK_NUMERAL"""
        p[0] = NumeralTerm(p[1])

    def p_app(self, p):
        """app : TK_LPAREN TK_SYMBOL term_star TK_RPAREN"""
        p[0] = FunctionApplicationTerm(p[2], p[3])

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

    def p_term(self, p):
        """term : symbol
                | numeral
                | app"""
        p[0] = p[1]       
    
    def p_declare_language(self, p):
        """declare_language : TK_LPAREN TK_DECLARE_LANGUAGE TK_LPAREN nonterminal_plus TK_RPAREN TK_LPAREN syntactic_rule_plus TK_RPAREN TK_RPAREN"""
        p[0] = DeclareLanguageCommand(p[4], p[7])
    
    def p_nonterminal_plus(self, p):
        """nonterminal_plus : nonterminal_plus nonterminal
                            | nonterminal"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]] 

    def p_nonterminal(self, p):
        """nonterminal : TK_LPAREN TK_SYMBOL sort TK_RPAREN"""
        p[0] = (p[2], p[3])

    def p_syntactic_rule_plus(self, p):
        """syntactic_rule_plus : syntactic_rule_plus syntactic_rule
                               | syntactic_rule"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]

    def p_syntactic_rule(self, p):
        """syntactic_rule : TK_LPAREN production_plus TK_RPAREN"""
        p[0] = SyntacticRule(p[2])

    def p_production_plus(self, p):
        """production_plus : production_plus production
                           | production"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]
    
    def p_production(self, p):
        """production : TK_LPAREN TK_PRODUCTION TK_SYMBOL sort_star TK_RPAREN """
        p[0] = ProductionRule(p[3], p[4])

    def p_declare_semantics(self, p):
        """declare_semantics : TK_LPAREN TK_DECLARE_SEMANTICS sem_plus TK_RPAREN"""
        p[0] = DeclareSemanticsCommand(p[3])

    def p_sem_plus(self, p):
        """sem_plus : sem_plus sem
                    | sem"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]

    def p_sem(self, p):
        """sem : TK_LPAREN TK_SYMBOL match term TK_RPAREN"""
        p[0] = SemanticRule(p[2], p[3], p[4])

    def p_match(self, p):
        """match : TK_LPAREN TK_PRODUCTION TK_SYMBOL var_star TK_RPAREN"""
        p[0] = ProductionMatch(p[3], p[4])

    def p_var_star(self, p):
        """var_star : var_plus
                    | """
        if 2 == len(p):
            p[0] = p[1]
        else:
            p[0] = []

    def p_var_plus(self, p):
        """var_plus : var_plus TK_SYMBOL
                    | TK_SYMBOL"""
        if 2 == len(p):
            p[0] = [p[1]]
        else:
            p[0] = p[1] + [p[2]]    

    def p_error(self, p):
        if p:
            print(f"Line {p.lineno}: Parsing error at '{p.value}'")
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

