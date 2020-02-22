from ir import *
from manual_parser import parse_specs
from collections import namedtuple, defaultdict
from manual_parser import get_spec_from_xml
from sig import get_inst_sigs
import io

def get_inst_pattern_ctor(inst):
  if inst.op in icmp_ops:
    matcher = f'm_Cmp_dont_care(CmpInst::Predicate::ICMP_{inst.op.upper()}, '
  elif inst.op in fcmp_ops:
    matcher = f'm_Cmp_dont_care(CmpInst::Predicate::FCMP_{inst.op.upper()[1:]}, '
  elif inst.op in commutative_binary_ops:
    matcher = f'm_c_{inst.op}('
  else:
    matcher = f'm_{inst.op}('

  assert inst.op not in binary_ops or len(inst.args) <= 2,\
      "flattend mul/xor/add/or/and not supported yet";
  return matcher

def get_const_pattern(const):
  return f'm_SpecificInt(APInt({const.bitwidth}, {const.value}ull))'

class VarGenerator:
  def __init__(self):
    self.counter = 0

  def new_var(self):
    v = 'tmp%d' % self.counter
    self.counter += 1
    return v

class BoundOperation:
  '''
  a rule is:
    * a list of *scalar* live ins
    * an expression dag

  '''
  def __init__(self, root, dag):
    var_generator = VarGenerator()

    liveins = []
    bound_liveins = []
    vars_to_declare = []
    livein2vars = defaultdict(list)
    def build_pattern(node_id, depth=1):
      node = dag[node_id]
      node_ty = type(node)
      if node_ty == Instruction:
        pattern_ctor = get_inst_pattern_ctor(node)
        sub_patterns = [build_pattern(arg, depth+1) for arg in node.args]
        indent = '  ' * (depth+2)
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
        vars_to_declare.append(x)
        livein2vars[node_id].append(x)
        return f'm_Value({x})'

    pattern = build_pattern(root)
    root_bitwidth = dag[root].bitwidth
    conds = [
        f'hasBitWidth(V, {root_bitwidth})',
        f'PatternMatch::match(const_cast<Value *>(V), {pattern})']
    for xs in livein2vars.values():
      conds.extend(f'{xs[0]} == {x}' for x in xs[1:])

    matching_cond = ' && '.join(conds)
    var_decls = ' '.join(f'Value *{x};' for x in vars_to_declare)
    self.matching_code = f'''
    {var_decls};
    bool Matched = {matching_cond};
    if (Matched)
      Matches.push_back({{ {', '.join(bound_liveins)} }});
    return Matched;
    '''
    self.liveins = liveins
    self.bound_liveins = bound_liveins
    self.livein2vars = livein2vars

  def __hash__(self):
    return hash(self.matching_code)

  def __eq__(self, other):
    return self.matching_code == other.matching_code

  def get_bound_liveins(self):
    '''
    return the dag nodes corresponding to `get_operation_liveins`
    '''
    return self.liveins

  def get_operation_liveins(self):
    '''
    return the temp vars we matched to this operation
    '''
    return self.bound_liveins

  def get_matching_code(self):
    return self.matching_code

class RuleCollection:
  '''
  represents either a single BoundOperation or a collection of mux'd BoundRules
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
  def __init__(self, sig, sema, out_ids, dag):
    self.sig = sig
    self.sema = sema
    self.lanes = []
    self.dag = dag
    for out_id in out_ids:
      if type(dag[out_id]) is not Mux:
        self.lanes.append(RuleCollection.just_one(BoundOperation(out_id, dag)))
      else:
        mux = dag[out_id]
        rules = [BoundOperation(v, dag) for _, v in mux.kv_pairs]
        keys = [k for k, _ in mux.kv_pairs]
        self.lanes.append(RuleCollection.many(rules, keys, mux.ctrl))
    self.lanes.reverse()

  def all_lanes_simple(self):
    return all(lane.num_rules() == 1 for lane in self.lanes)

  def rules(self):
    rules = []
    for lane in self.lanes:
      rules.extend(lane.rules)
    return rules

  def emit_bundel_desc(self, outf):
    pass

class RuleBundleIndex:
  '''
  rule index is a reverse index that maps:
    <rule> -> [<lane id>, <rule bundle>]
  '''

  def __init__(self, bundles):
    # inst -> [bundle]
    self.bundles = bundles

  def emit_matchers(self):
    pass

  def emit_index(self):
    pass

def declare_operation(op_name, bound_operation):
  return f'''
class : public Operation {{
  virtual bool numLiveins() const override {{
    return { len(bound_operation.liveins) };
  }}

  virtual bool match(
    const Value *V, std::vector<Match> &Matches) const override {{
    { bound_operation.get_matching_code() }
  }}
}} {op_name};
  '''

def emit_slice(liveins, s):
  '''
  `s` is a slice, slicing one of the `liveins` (list of z3 vars)
  '''
  assert isinstance(s, Slice)
  input_names = [x.decl().name() for x in liveins]
  input_id = input_names.index(s.base)
  return f'InputSlice {{ {input_id}, {s.lo}, {s.hi} }}'

# FIXME: assert that we only have a single output
def emit_sig(sig):
  xs, ys = sig
  input_sizes = ', '.join(str(x.bitwidth) for x in xs)
  output_sizes = ', '.join(str(y_size) for y_size in ys)
  has_imm8 = 'true' if any(x.is_constant for x in xs) else 'false'
  return f'InstSignature {{ {{ {input_sizes} }}, {{ {output_sizes} }}, {has_imm8} }}' 

def codegen(bundles):
  '''
  bundles : mapping inst -> bundles
  '''
  operation_names = {}
  operation_defs = {}
  inst_defs = {}
  for inst, bundle in bundles.items():
    liveins, _ = bundle.sema
    # BoundOperation for each lane
    bound_ops = []
    for lane in bundle.lanes:
      [op] = lane.rules
      # emit this operation if we haven't yet
      if op not in operation_defs:
        op_id = len(operation_defs)
        op_name = 'Operation%d' % op_id
        operation_names[op] = op_name
        operation_defs[op] = declare_operation(op_name, op)

      bound_liveins = [emit_slice(liveins, bundle.dag[x]) for x in op.get_bound_liveins()]
      bound_ops.append(
          f'BoundOperation(&{op_name}, {{ { ", ".join(bound_liveins) } }})')
    sig = emit_sig(bundle.sig)
    inst_defs[inst] = f'InstBinding("{inst}", {sig}, {{ {", ".join(bound_ops)} }})'

  op_decls = '\n'.join(op_decl for op_decl in operation_defs.values()) 
  inst_bindings = ',\n'.join(inst_def for inst_def in inst_defs.values()) 
  return f'''
{op_decls}
std::vector<InstBinding> Insts {{ 
  {inst_bindings}
}};
  '''

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

  bundles = {}
  for inst, (_, out_ids, dag) in lifted.items():
    try:
      rb = RuleBundle(sigs[inst], semas[inst], out_ids, dag)
      if not rb.all_lanes_simple():
        continue
      bundles[inst] = rb 
    except AssertionError as e:
      pass

  with open('InstSema.cpp', 'w') as f:
    f.write('''
#include "InstSema.h"

using namespace llvm;
using namespace PatternMatch;
    ''')
    f.write(codegen(bundles))

  exit()

  rbi = RuleBundleIndex(bundles)
  all_conds = set()
  for inst, rb in rbi.bundles.items():
    conds = {
        r.get_matching_code()
        for r in rb.rules()}
    all_conds.update(conds)
    print(inst)
    pprint(conds)
  print('Total number of matching rules:', len(all_conds))

  _, outs, dag = lifted['_mm512_avg_epu16']
  br = BoundOperation(outs[0], dag)
  print(br.get_matching_code())
  print(list(zip(br.get_bound_liveins(), br.get_operation_liveins())))
  print(list(zip(br.get_operation_liveins(),
    (dag[x] for x in br.get_bound_liveins()))))