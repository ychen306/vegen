from ir import *
from collections import namedtuple, defaultdict
import io

var_counter = 0
def new_var():
  global var_counter
  var_counter += 1
  return 'tmp%d' % var_counter

def emit_inst_matcher(x, inst):
  '''
  match an ir value `x` to `inst`,
  return ([<the matching condition>], [<fresh var bound to operand of inst>]
  '''
  if inst.op in icmp_ops:
    matcher = f'm_ICmp(ICMP_{inst.op.upper()}, '
  elif inst.op in fcmp_ops:
    matcher = f'm_ICmp(FCMP_{inst.op.upper()[1:]}, '
  else:
    matcher = f'm_{inst.op}('

  bound_vars = [new_var() for _ in inst.args]
  conds = [
      '{matcher}{binding}).match({x})'
      .format( 
        matcher=matcher,
        binding=', '.join(f'm_Value({x2})' for x2 in bound_vars),
        x=x
        )]
  return conds, bound_vars

def emit_const_matcher(x, const):
  '''
  match an ir value `x` to a constant.
  return a list of matching condition
  '''
  return [
      f'm_SpecificInt(APInt({const.bitwidth}, {const.value})).match({x})']

class BoundRule:
  '''
  a rule is:
    * a list of *scalar* live ins
    * an expression dag

  '''
  def __init__(self, root, dag):
    # conditions for a match
    conds = []
    # mapping <matched ir value> -> <dag node id>
    var2node = {}

    livein2vars = defaultdict(list)
    # a unique, sorted list of variables representing the bound live ins
    liveins = []

    def emit_rec(x):
      node_id = var2node[x]
      node = dag[node_id]
      node_ty = type(node)
      if node_ty == Instruction:
        inst_conds, bound = emit_inst_matcher(x, node)
        conds.extend(inst_conds)
        var2node.update({
          x2: node_id2
          for x2, node_id2 in zip(bound, node.args)})
        for x2 in bound:
          emit_rec(x2)
      elif node_ty == Constant:
        conds.extend(emit_const_matcher(x, node))
      else:
        if len(livein2vars[node_id]) == 0:
          liveins.append(x)
        livein2vars[node_id].append(x)

    # in case we have more than one values bound to the same live-in
    # insert additional constraint that force them to be the same value
    for xs in livein2vars.values():
      conds.extend(f'{xs[0]} == {x2}' for x2 in xs[1:])

    buf = io.StringIO()
    var2node['root'] = root
    emit_rec('root')
    # declare values for the bound variables
    for x in var2node.keys():
      if x == 'root':
        continue
      buf.write(f'\tValue *{x};\n')
    buf.write('\tif ({conds})\n'.format(conds=' &&\n\t\t'.join(conds)))

    self.matcher = buf.getvalue()
    self.liveins = liveins

  def get_livein_binding(self):
    return self.liveins

  def get_matcher(self):
    return self.matcher

class RuleBundle:
  '''
  we represent a vector instruction as a bundle of rules
  we a group of scalar ir values if:
    * these values are independent
    * all rules in the bundle are matched

  we need to generate this to a C++ file so we can use it in LLVM
  And in C++, we represent a bundle as a this:
    [(<binding>, <rule id>), ...]
  Where a binding is a mapping:
    <rule live-in> -> <live-in lane>

  this means that we can uniform vector insts like padd is basically
   one rule but with 4 bindings
  '''
  def __init__(self, liveins, out_ids, dag):
    pass

  def get_rules(self):
    '''
    '''
    pass

  def emit_bundel_desc(self, outf):
    pass

class RuleBundleIndex:
  '''
  rule index is a reverse index that maps:
    <rule> -> [<lane id>, <rule bundle>]
  '''

  def __init__(self):
    pass

  def add_rule_bundle(self, bundle):
    pass

  def emit_matchers(self):
    pass

  def emit_index(self):
    pass

if __name__ == '__main__':
  import sys
  import pickle

  lifted_f = sys.argv[1]
  with open(lifted_f, 'rb') as f:
    lifted = pickle.load(f)

  _, outs, dag = lifted['_mm512_avg_epu16']
  br = BoundRule(outs[0], dag)
  print(br.get_matcher())
