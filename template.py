from parser import SpyroSygusParser

LOGIC = 0
VARIABLES = 1
RELATIONS = 2
GENERATOR = 3
EXAMPLE = 4
FUNCTIONS = 5

class Template():
    def __init__(self, template):
        self.parser = SpyroSygusParser()
        self.__ast = self.parser.parse(template)

    def get_logic(self):
        return self.__ast[LOGIC]