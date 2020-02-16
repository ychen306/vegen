from ir import *
from collections import namedtuple, defaultdict
import xml.etree.ElementTree as ET
from manual_parser import get_spec_from_xml
from sig import get_intrinsic_signature, InputType
import io

def get_inst_pattern_ctor(inst):
  if inst.op in icmp_ops:
    matcher = f'm_c_ICmp_dont_care(ICMP_{inst.op.upper()}, '
  elif inst.op in fcmp_ops:
    matcher = f'm_FCmp(FCMP_{inst.op.upper()[1:]}, '
  elif inst.op in commutative_binary_ops:
    matcher = f'm_c_{inst.op}('
  else:
    matcher = f'm_{inst.op}('

  assert inst.op not in binary_ops or len(inst.args) <= 2,\
      "flattend mul/xor/add/or/and not supported yet";
  return matcher

def get_const_pattern(const):
  return f'm_SpecificInt(APInt({const.bitwidth}, {const.value}))'

class VarGenerator:
  def __init__(self):
    self.counter = 0

  def new_var(self):
    v = 'tmp%d' % self.counter
    self.counter += 1
    return v

class BoundRule:
  '''
  a rule is:
    * a list of *scalar* live ins
    * an expression dag

  '''
  def __init__(self, root, dag):
    var_generator = VarGenerator()

    liveins = []
    bound_liveins = []
    livein2vars = defaultdict(list)
    def build_pattern(node_id, depth=1):
      node = dag[node_id]
      node_ty = type(node)
      if node_ty == Instruction:
        pattern_ctor = get_inst_pattern_ctor(node)
        sub_patterns = [build_pattern(arg, depth+1) for arg in node.args]
        indent = '  ' * depth
        ctor_args = ',\n'.join(indent+p for p in sub_patterns)
        # pattern_ctor already has open parenthesis
        return f'{pattern_ctor}\n{ctor_args})'
      elif node_ty == Constant:
        return get_const_pattern(node)
      else:
        x = var_generator.new_var()
        # first time seeing a live-in
        if len(livein2vars[node_id]) == 0:
          liveins.append(node_id)
          bound_liveins.append(x)
        livein2vars[node_id].append(x)
        return f'm_Value({x})'

    pattern = build_pattern(root)
    root_bitwidth = dag[root].bitwidth
    conds = [
        f'hasBitWidth(root, {root_bitwidth})',
        f'match(root, {pattern})']
    for xs in livein2vars.values():
      conds.extend(f'{xs[0]} == {x}' for x in xs[1:])

    self.matching_cond = ' && '.join(conds)
    self.liveins = liveins
    self.bound_liveins = bound_liveins
    self.livein2vars = livein2vars

  def get_rule_liveins(self):
    return self.liveins

  def get_bound_liveins(self):
    return self.bound_liveins

  def get_matching_cond(self):
    return self.matching_cond

class RuleCollection:
  '''
  represents either a single BoundRule or a collection of mux'd BoundRules
  '''
  def __init__(self, rules, mux_keys=None, mux_control=None):
    self.rules = rules 
    self.mux_keys = mux_keys

  @staticmethod
  def just_one(rule):
    return RuleCollection([rule])

  @staticmethod
  def many(rules, mux_keys, mux_control):
    return RuleCollection(rules, mux_keys, mux_control)

  def num_rules(self):
    return len(self.rules)

  def is_muxed(self):
    return len(self.rules) > 1

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
  # FIXME: detect when a rule (or one of the muxed rule) doesn't
  # do computation (e.g. not starting with an instruction) so
  # the packing heuristics knows this
  def __init__(self, liveins, livein_types, out_ids, dag):
    self.lanes = []
    self.dag = dag
    for out_id in out_ids:
      if type(dag[out_id]) is not Mux:
        self.lanes.append(RuleCollection.just_one(BoundRule(out_id, dag)))
      else:
        mux = dag[out_id]
        rules = [BoundRule(v, dag) for _, v in mux.kv_pairs]
        keys = [k for k, _ in mux.kv_pairs]
        self.lanes.append(RuleCollection.many(rules, keys, mux.ctrl))

  def rules(self):
    for lane in self.lanes:
      yield from lane.rules

  def emit_bundel_desc(self, outf):
    pass

class RuleBundleIndex:
  '''
  rule index is a reverse index that maps:
    <rule> -> [<lane id>, <rule bundle>]
  '''

  def __init__(self, sigs, semas, lifted):
    self.bundles = {}
    for inst, (_, out_ids, dag) in lifted.items():
      try:
        self.bundles[inst] = RuleBundle(sigs[inst], semas[inst], out_ids, dag)
      except AssertionError:
        pass
    print(len(self.bundles))

  def emit_matchers(self):
    pass

  def emit_index(self):
    pass

def parse_specs(spec_f):
  specs = {}
  
  for intrin in ET.parse(spec_f).iter('intrinsic'):
    try:
      spec = get_spec_from_xml(intrin)
      specs[spec.intrin] = spec
    except:
      continue
  return specs

def get_inst_sigs(semas, specs):
  sigs = {}
  for inst, (in_vals, out_vals) in semas.items():
    if inst in specs:
      sigs[inst] = get_intrinsic_signature(specs[inst])
    else:
      input_types = tuple(InputType(x.size(), is_constant=False) for x in in_vals)
      output_sizes = tuple(y.size() for y in out_vals)
      sigs[inst] = input_types, output_sizes
  return sigs

if __name__ == '__main__':
  import sys
  import pickle
  from semas import semas
  from pprint import pprint
  
  specs = parse_specs('data-latest.xml')
  sigs = get_inst_sigs(semas, specs)

  lifted_f = sys.argv[1]
  with open(lifted_f, 'rb') as f:
    lifted = pickle.load(f)

  rbi = RuleBundleIndex(sigs, semas, lifted)
  all_conds = set()
  for inst, rb in rbi.bundles.items():
    conds = {
        r.get_matching_cond()
        for r in rb.rules()}
    all_conds.update(conds)
    print(inst)
    pprint(conds)
  print('Total number of matching rules:', len(all_conds))

  exit()
  _, outs, dag = lifted['_mm512_avg_epu16']
  br = BoundRule(outs[0], dag)
  print(br.get_matching_cond())
  print(list(zip(br.get_rule_liveins(), br.get_bound_liveins())))
  print(list(zip(br.get_bound_liveins(),
    (dag[x] for x in br.get_rule_liveins()))))
