import ply.lex

class SpyroSygusLexer(object):
    reserved = {
        'set-logic': 'TK_SET_LOGIC',
        'define-var': 'TK_DEFINE_VARIABLE',
        'define-rel': 'TK_DEFINE_RELATION',
        'generator': 'TK_DEFINE_GENERATOR',
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
    t_TK_RPAREN = r'\)'

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

    @ply.lex.TOKEN(_numeral)
    def t_TK_NUMERAL(self, t):
        t.value = int(t.value)
        return t

    @ply.lex.TOKEN(_symbol)
    def t_TK_SYMBOL(self, t):
        t.type = self.reserved.get(t.value, 'TK_SYMBOL')
        return t

    def __init__(self):
        self.lexer = ply.lex.lex(object=self, debug=0)

    def lex(self, input_string):
        self.lexer.input(input_string)
        
        while True:
            tok = self.lexer.token()
            if tok in None:
                break
            else:
                yield tok

    def t_error(self, t):
        print("Illegal character %s" % repr(t.value[0]))
        t.lexer.skip(1)