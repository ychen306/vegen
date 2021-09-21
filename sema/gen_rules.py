from ir import *
from collections import namedtuple, defaultdict
import io
import json
import functools
from canonicalize import canonicalize

SelectOnCmp = namedtuple('SelectOnCmp', ['op', 'a', 'b', 'true_val', 'false_val'])

def get_const_pattern(const):
  return f'm_SpecificInt(APInt({const.bitwidth}, "{const.value}", 10))'

def match_select_on_cmp(node_id, dag):
  select = dag[node_id]
  if not isinstance(select, Instruction) or select.op != 'Select':
    return None

  cond, true_val, false_val = select.args
  cond = dag[cond]
  if not isinstance(cond, Instruction) or cond.op not in cmp_ops:
    return None

  a, b = cond.args
  return SelectOnCmp(cond.op, a, b, true_val, false_val)

class VarGenerator:
  def __init__(self):
    self.counter = 0

  def new_var(self):
    v = 'tmp%d' % self.counter
    self.counter += 1
    return v

def select_cmp_pred(op):
  if op in icmp_ops:
    return f'CmpInst::Predicate::ICMP_{op.upper()}'

  assert op in fcmp_ops
  return f'CmpInst::Predicate::FCMP_{op.upper()[1:]}'

class BoundOperation:
  '''
  a rule is:
    * a list of *scalar* live ins
    * an expression dag

  '''
  def __init__(self, root, dag):
    try:
      dag, root = canonicalize(dag, root)
    except:
      dag, root = dag, root

    var_generator = VarGenerator()

    # FIXME : make liveins a list of nodes instead of node ids
    liveins = []
    bound_liveins = []
    vars_to_declare = []
    livein2vars = defaultdict(list)

    def build_pattern(node_id, depth=1, max_depth=100):
      assert depth < max_depth
      node = dag[node_id]
      node_ty = type(node)
      indent_unit = '  '
      indent = indent_unit * (depth+2)

      if node_ty == Instruction:
        args = node.args

        soc = match_select_on_cmp(node_id, dag)
        if soc is not None:
          # soc ::= (a op b) ? true_val : false_val
          args = soc.a, soc.b, soc.true_val, soc.false_val
          pattern_ctor = f'm_SelectOnCmp({select_cmp_pred(soc.op)},'
        elif node.op in cmp_ops:
          pattern_ctor = 'm_CmpWithPred(' + select_cmp_pred(node.op) + ', '
        elif node.op in commutative_binary_ops:
          pattern_ctor = f'm_c_{node.op}('
        else:
          pattern_ctor = f'm_{node.op}('

        assert node.op not in binary_ops or len(node.args) <= 2,\
            "flattend mul/xor/add/or/and not supported yet";

        sub_patterns = [build_pattern(arg, depth+1) for arg in args]
        ctor_args = ',\n'.join(indent+p for p in sub_patterns)
        # pattern_ctor already has open parenthesis
        return f'{pattern_ctor}\n{ctor_args})'
      elif node_ty == Constant:
        return get_const_pattern(node)
      else:
        assert node_ty == Slice
        x = var_generator.new_var()
        # first time seeing a live-in
        if len(livein2vars[node_id]) == 0:
          liveins.append(node)
          bound_liveins.append(x)
        vars_to_declare.append(x)
        livein2vars[node_id].append(x)
        return f'm_Value({x})'

    self.is_nop = type(dag[root]) not in (Instruction, Constant)
    pattern = build_pattern(root)
    root_bitwidth = dag[root].bitwidth
    conds = [
        f'hasBitWidth(V, {root_bitwidth})',
        f'PatternMatch::match(V, {pattern})']
    for livein, xs in livein2vars.items():
      # assert that the liveins have the right size
      conds.append(f'hasBitWidth({xs[0]}, {dag[livein].bitwidth})')
      # assert that the matched live-ins are consistent
      conds.extend(f'{xs[0]} == {x}' for x in xs[1:])

    matching_cond = ' &&\n'.join(conds)
    var_decls = ' '.join(f'Value *{x};' for x in vars_to_declare)
    self.matching_code = f'''
    {var_decls}
    bool Matched = {matching_cond};
    if (Matched)
      Matches.push_back({{
      false,
      // matched live ins
      {{ {', '.join(bound_liveins)} }},
      // the matched value itself
      V
      }});
    return Matched;
    '''
    self.liveins = liveins
    self.bound_liveins = bound_liveins
    self.livein2vars = livein2vars
    self.bitwidth = root_bitwidth

  def __hash__(self):
    return hash(self.matching_code)

  def __eq__(self, other):
    return self.matching_code == other.matching_code

  def __ne__(self, other):
    return self.matching_code != other.matching_code

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
      self.lanes.append(RuleCollection.just_one(BoundOperation(out_id, dag)))
    self.lanes.reverse()

  def all_lanes_simple(self):
    return all(lane.num_rules() == 1 for lane in self.lanes)

  def has_nop(self):
    return any(lane.rules[0].is_nop for lane in self.lanes)

  def rules(self):
    rules = []
    for lane in self.lanes:
      rules.extend(lane.rules)
    return rules

def declare_operation(op_name, bound_operation):
  return f'''
class : public Operation {{
  bool match(
    Value *V, SmallVectorImpl<Match> &Matches) const override {{
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
  input_sizes = ', '.join(str(x.bitwidth) for x in sig.inputs)
  has_imm8 = 'true' if any(x.is_constant for x in sig.inputs) else 'false'
  return f'InstSignature {{ {{ {input_sizes} }}, {{ {str(sig.output.bitwidth)} }}, {has_imm8} }}'

def codegen(bundles, inst_features, costs, binding_vector_name='Insts'):
  '''
  bundles : mapping inst -> bundles
  '''
  operation_names = {}
  operation_defs = {}
  inst_defs = {}
  for inst, bundle in bundles.items():
    features = inst_features[inst]
    feature_list = ', '.join(f'"{f}"' for f in features)
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
      else:
        op_name = operation_names[op]

      bound_liveins = [emit_slice(bundle.sema.inputs, x) for x in op.get_bound_liveins()]
      bound_ops.append(
          f'\n    BoundOperation(&{op_name}, {{ { ", ".join(bound_liveins) } }})')
    sig = emit_sig(bundle.sig)
    cost = costs[inst]
    inst_defs[inst] = f'  InstBinding("{inst}", {{ {feature_list} }}, {sig}, {{ {", ".join(bound_ops)} }}, {cost})'

  op_decls = '\n'.join(op_decl for op_decl in operation_defs.values())
  inst_bindings = ',\n'.join(inst_def for inst_def in inst_defs.values())
  return f'{op_decls}\nstd::vector<InstBinding> {binding_vector_name} {{\n{inst_bindings}\n}};'
