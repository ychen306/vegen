import ply.lex as lex
from sema_ast import Number, Var

# TODO: lex hex literal

reserved = {
    'FOR',
    'ENDFOR',

    'CASE',
    'OF',
    'ESAC',

    'IF',
    'THEN',
    'ELSE',
    'FI',

    'DO',
    'WHILE',
    'OD',

    'TO',
    'DOWNTO',

    'BREAK',

    'RETURN',
    'DEFINE',

    'OP',

    'AND', 'OR', 'XOR', 'NOT',
    }

binary_ops = {
    r'<<': 'LSHIFT',
    r'>>' : 'RSHIFT',
    r'<<<': 'LSHIFT_LOGICAL',
    r'>>>' : 'RSHIFT_LOGICAL',

    r'+':  'PLUS',
    r'-':  'MINUS',

    r'+=': 'PLUS_EQUAL',
    r'|=': 'OR_EQUAL',

    r'*':  'TIMES',
    r'/':  'DIV',
    r'%':  'MOD',

    r'<': 'LESS',
    r'>': 'GREATER',
    r'<=': 'LESS_EQUAL',
    r'>=': 'GREATER_EQUAL',

    r'==': 'EQUAL',
    r'!=': 'NOT_EQUAL',

    r'~':  'BITWISE_NOT',

    r'&':  'BITWISE_AND',
    r'|':  'BITWISE_OR',
    }

tokens = [
    'PSEUDO', 'ID', 'COMMENT', 'NUMBER',
    'LBRACE', 'RBRACE', 'COLON',
    'UPDATE', 'SEMICOLON',
    'LPAREN', 'RPAREN', 'COMMA',
    'DOT',
    'LBRACKET', 'RBRACKET',
    'QUEST',

    'CASE_HEADER',

    # pseudo token
    'NEG'
    ] + list(binary_ops.values()) + list(reserved)

binary_regexp = r'|'.join(binary_ops)

def t_pseudo(t):
  r'\n\s*//.*'
  lexed = t.value 
  t.value = lexed[lexed.index('/') + 2:]
  t.type = 'PSEUDO'
  return t

def t_CASE_HEADER(t):
  r'\n\s*\d+:|\n\s*DEFAULT:|\n\s*[a-zA-Z_][a-zA-Z_0-9]*:'
  if t.value.strip().startswith('DEFAULT'):
    t.value = None
  else:
    try:
      value = int(t.value[:-1])
      t.value = Number(value)
    except:
      t.value = Var(t.value[:-1])
  return t

def t_binary(t):
  r'\|=|\+=|<<<?|>>>?|\+|\-|\*|/(?!/)|<=|>=|<|>|==|!=|%|~|&(?!&)|\|(?!\|)'
  t.type = binary_ops[t.value]
  return t

def t_not(t):
  r'!'
  t.type = 'NOT'
  return t

def t_and(t):
  r'&&'
  t.type = 'AND'
  return t

def t_or(t):
  r'\|\|'
  t.type = 'OR'
  return t

# pseudo code
def t_PSEUDO(t):
  r'\*.*\*'
  t.value = t.value[1:-1]
  return t

def t_ID(t):
  r'[a-zA-Z_][a-zA-Z_0-9]*'
  lexed = t.value.upper()
  if lexed in reserved:
    t.type = lexed
    t.value = lexed
  return t

def t_COMMENT(t):
  r'//.*|;'
  pass

# TODO: multiline comment?

def t_NUMBER(t):
  r'\d+\.\d*|0x[0-9a-fA-F]+|\d+'
  base = 16 if t.value.startswith('0x') else 10
  try:
    t.value = int(t.value, base)
  except:
    t.value = float(t.value)
  return t

def t_newline(t):
  r'\n|\\\n'
  t.lexer.lineno += 1

def t_error(t):
  raise SyntaxError('Lexer error')

t_LBRACE = r'\['
t_RBRACE = r'\]'
t_LBRACKET = r'{'
t_RBRACKET = r'}'
t_COLON = r':'
t_UPDATE = r'←|=|:='
t_SEMICOLON = ';'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_DOT = r'\.'
t_COMMA = r','
t_QUEST = r'\?'
t_ignore  = ' \t'

lexer = lex.lex()
if __name__ == '__main__':
  test_spec = '''
  CASE 0 OF
0: // individual-address invalidation retaining global translations
	OP_PCID := descriptor[11:0]
	ADDR := descriptor[127:64]
	BREAK
//1: // single PCID invalidation retaining globals
//	OP_PCID := descriptor[11:0]
//	// invalidate all mappings tagged with OP_PCID except global translations
//	BREAK
//2: // all PCID invalidation
//	// invalidate all mappings tagged with any PCID
//	BREAK
//3: // all PCID invalidation retaining global translations
//	// invalidate all mappings tagged with any PCID except global translations
//	BREAK
ESAC
      '''
  lexer.input(test_spec)
  for token in iter(lexer.token, None):
    print(token.type, token.value)
