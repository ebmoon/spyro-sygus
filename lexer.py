import ply.lex as lex

class SpyroSygusLexer(object):
    reserved = {
        'variables': 'TK_DEFINE_VARIABLES',
        'relations': 'TK_DEFINE_RELATIONS',
        'generator': 'TK_DEFINE_GENERATOR',
        'example': 'TK_DEFINE_EXAMPLE',
        'define-fun': 'TK_DEFINE_FUN',
        'Constant': 'TK_CONSTANT'
    }
    
    tokens = [
        'TK_LPAREN',
        'TK_RPAREN',
        'TK_NUMERAL',
        'TK_SYMBOL'
    ]

    tokens += list(set(reserved.values()))

    t_TK_LPAREN = r'\('
    t_TK_LPAREN = r'\)'

    _zero = r'0'
    _nonzero = r'[1-9]'
    _digit = r'[0-9]'
    _numeral = f'(?:{_zero})|(?:{_nonzero}(?:{_digit})*)'
    _symbolcc = r'(?:[a-zA-Z_&!~<>=/%]|@|\+|-|\*|\||\?|\.|\$|\^)'
    _symbol = f'{_symbolcc}(?:(?:{_symbolcc})|(?:{_digit}))*'

    t_ignore = ' \t\f\r'

    def t_newline(self, t):
        r'\n'
        t.lexer.lineno += 1

    def t_comment(self, t):
        r';.*'
        pass

    @ply.tex.TOKEN(_numeral)
    def t_TK_NUMERAL(self, t):
        t.value = int(t.value)
        return t

    @ply.tex.TOKEN(_symbol)
    def t_TK_SYMBOL(self, t):
        return t


    def __init__(self):
        self.lexer = lex.lex(object=self, debug=0)

    def lex(self, input_string):
        self.lexer.input(input_string)
        
        while True:
            tok = self.lexer.token()
            if tok in None:
                break
            else:
                yield tok

def t_error(t):
    print("Illegal character %s" % repr(t.value[0]))
    t.lexer.skip(1)

lexer = lex.lex(debug=0)