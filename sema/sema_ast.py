from collections import namedtuple

BitSlice = namedtuple('BitSlice', ['bv', 'hi', 'lo'])
Var = namedtuple('Var', ['name'])
Number = namedtuple('Number', ['val'])
Update = namedtuple('Update', ['lhs', 'rhs'])
OpUpdate = namedtuple('OpUpdate', ['op_name'])
# inc is a flag specifying whether we increment of decrement the induction variable
For = namedtuple('For', ['iterator', 'begin', 'end', 'body', 'inc'])
While = namedtuple('While', ['cond', 'body'])
If = namedtuple('If', ['cond', 'then', 'otherwise'])
Call = namedtuple('Call', ['func', 'args'])
BinaryExpr = namedtuple('BinaryExpr', ['op', 'a', 'b', 'expr_id'])
UnaryExpr = namedtuple('UnaryExpr', ['op', 'a'])
PseudoExpr = namedtuple('PseudoExpr', ['desc'])
PseudoStmt = namedtuple('PseudoStmt', ['desc'])
Return = namedtuple('Return', ['val'])
Select = namedtuple('Select', ['cond', 'then', 'otherwise'])
RegSel = namedtuple('RegSel', ['base', 'idx'])
Match = namedtuple('Match', ['val', 'cases'])
Case = namedtuple('Case', ['val', 'stmts'])
# property lookup
Lookup = namedtuple('Lookup', ['obj', 'key'])
FuncDef = namedtuple('FuncDef', ['name', 'params', 'body'])
Break = namedtuple('Break', [])

Parameter = namedtuple('Parameter', ['name', 'type'])
Spec = namedtuple('Spec', [
  'intrin', 'inst', 'params',
  'spec', 'rettype', 'binary_exprs',

  'inst_form',

  # configuration of binary exprs
  'configs',
  ])
