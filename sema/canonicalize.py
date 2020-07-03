from ir import *
from llvmlite import ir as llir
import llvmlite.binding as llvm
from functools import partial

def get_ordered_liveins(dag, root):
  '''
  Get the set of live-ins of the sub-dag rooted at `root`, and fix the ordering
  '''
  live_ins = []
  visited = set()
  def visit(v):
    if v in visited:
      return
    visited.add(v)

    node = dag[v]
    if isinstance(node, Instruction):
      for arg in node.args:
        visit(arg)
    elif isinstance(node, Mux):
      for _, val in node.kv_pairs:
        visit(val)
    elif isinstance(node, Slice):
      live_ins.append(node)

  visit(root)
  return live_ins

class BuildError(Exception):
  pass

inst_constructors = {
    'AShr': 'ashr',
    'Add': 'add',
    'And': 'and_',
    'FAdd': 'fadd',
    'FDiv': 'fdiv',
    'FMul': 'fmul',
    'FRem': 'frem',
    'FSub': 'fsub',
    'LShr': 'lshr',
    'Mul': 'mul',
    'Or': 'or_',
    'SDiv': 'sdiv',
    'SRem': 'srem',
    'Shl': 'shl',
    'Sub': 'sub',
    'UDiv': 'udiv',
    'URem': 'urem',
    'Xor': 'xor',
    'Select': 'select'}

# mapping *some* llvm opcodes back to opcode of our ir
llvm_opcodes = {
    'trunc': 'Trunc',
    'sext': 'SExt',
    'zext': 'ZExt',

    'select': 'Select',

    'add': 'Add',
    'and': 'And',
    'ashr': 'AShr',
    'fadd': 'FAdd',
    'fdiv': 'FDiv',
    'fmul': 'FMul',
    'frem': 'FRem',
    'fsub': 'FSub',
    'lshr': 'LShr',
    'mul': 'Mul',
    'or': 'Or',
    'sdiv': 'SDiv',
    'select': 'Select',
    'shl': 'Shl',
    'srem': 'SRem',
    'sub': 'Sub',
    'udiv': 'UDiv',
    'urem': 'URem',
    'xor': 'Xor'}

# mapping *some* llvm predicate to our comparison ir opcode
predicates = {
    'eq': 'Eq',
    'ne': 'Ne',
    'ugt': 'Ugt',
    'uge': 'Uge',
    'ult': 'Ult',
    'ule': 'Ule',
    'sgt': 'Sgt',
    'sge': 'Sge',
    'slt': 'Slt',
    'sle': 'Sle',
    'oeq': 'Foeq',
    'one': 'Fone',
    'ogt': 'Fogt',
    'oge': 'Foge',
    'olt': 'Folt',
    'ole': 'Fole',
    }

def get_inst_ctor(builder, inst):
  op = inst.op
  if op in inst_constructors:
    return getattr(builder, inst_constructors[op])
  if op in ('SExt', 'ZExt', 'Trunc'):
    return partial(getattr(builder, op.lower()), typ=llir.IntType(inst.bitwidth))
  cmp_ctors = {
      'Eq': partial(builder.icmp_unsigned, '=='),
      'Ne': partial(builder.icmp_unsigned, '!='),

      'Ugt': partial(builder.icmp_unsigned, '>'),
      'Uge': partial(builder.icmp_unsigned, '>='),
      'Ult': partial(builder.icmp_unsigned, '<'), 
      'Ule': partial(builder.icmp_unsigned, '<='),

      'Sgt': partial(builder.icmp_signed, '>'), 
      'Sge': partial(builder.icmp_signed, '>='), 
      'Slt': partial(builder.icmp_signed, '<'), 
      'Sle': partial(builder.icmp_signed, '<='),

      'Foeq': partial(builder.icmp_unsigned, '=='),
      'Fone': partial(builder.icmp_unsigned, '!='),
      'Fogt': partial(builder.icmp_unsigned, '>'),
      'Foge': partial(builder.icmp_unsigned, '>='),
      'Folt': partial(builder.icmp_unsigned, '<'), 
      'Fole': partial(builder.icmp_unsigned, '<='),
      }
  if op not in cmp_ctors:
    raise BuildError('Unsupported op %s' % op)
  return cmp_ctors[op]

def parse_llvm_opcode(inst):
  if inst.opcode in llvm_opcodes:
    return llvm_opcodes[inst.opcode]

  assert inst.opcode in ('icmp', 'fcmp')

  # Hacky way to parse predicate because
  # llvmlite doesn't have a proper API for this
  tokens = str(inst).split()
  _, _, pred, *_ = tokens[tokens.index('='):]
  assert pred in predicates
  return predicates[pred]

def parse_llvm_bitwidth(ty):
  type2bitwidth = {
      'i1' : 1,
      'i8' : 8,
      'i16': 16,
      'i32': 32,
      'i64': 32,
      'float': 32,
      'double': 64,
      }
  bw = type2bitwidth.get(str(ty))
  assert bw is not None
  return bw

def parse_llvm_arg(ll2ir, dag, arg):
  '''
  ll2ir maps <llvm value> -> <ir node id>
  '''
  val = ll2ir.get(str(arg))
  if val is not None:
    return val
  tokens = str(arg).split()
  # Bail out if the argument doesn't look some thing like `i32 C`
  assert(len(tokens) == 2)
  ty, val = tokens
  c = Constant(bitwidth=parse_llvm_bitwidth(ty), value=int(val))
  val_id = len(ll2ir)
  ll2ir[str(arg)] = val_id
  dag[val_id] = c
  return val_id

def canonicalize(dag, root):
  '''
  build an llir module containing a single function that 
  implements `dag` with a single basic block
  '''
  live_ins = get_ordered_liveins(dag, root)

  arg_types = [llir.IntType(x.bitwidth) for x in live_ins]
  ret_ty = llir.IntType(dag[root].bitwidth)
  func_ty = llir.FunctionType(ret_ty, arg_types)

  module = llir.Module()
  func = llir.Function(module, func_ty, name="wrapper")
  bb = func.append_basic_block(name="entry")
  builder = llir.IRBuilder(bb)

  # map rule arg -> arg
  ir_args = { arg : ir_arg for arg, ir_arg in zip(live_ins, func.args) }

  # mapping node value -> ir value
  ir_values = {}
  def emit(v):
    if v in ir_values:
      return ir_values[v]

    node = dag[v]
    if isinstance(node, Instruction):
      args = [emit(arg) for arg in node.args]
      ir_val = get_inst_ctor(builder, node)(*args)
    elif isinstance(node, Constant):
      # FIXME: what happens when there's float constant?
      ty = llir.IntType(node.bitwidth)
      ir_val = llir.Constant(ty, node.value)
    elif isinstance(node, Mux):
      # we only support two-way mux, which maps to select
      if len(node.kv_pairs) != 2:
        raise BuildError("only support two-way mux")

      false_branch, true_branch = node.kv_pairs
      assert true_branch[0] == 1
      ctrl_val = emit(node.ctrl)
      true_val = emit(true_branch[1])
      false_val = emit(false_branch[1])
      ir_val = builder.select(ctrl_val, true_val, false_val)
    else:
      assert isinstance(node, Slice)
      ir_val = ir_args[node]

    ir_values[v] = ir_val
    return ir_val

  builder.ret(emit(root))

  pmb = llvm.create_pass_manager_builder()
  pmb.opt_level = 3
  pm = llvm.create_module_pass_manager()
  pmb.populate(pm)

  llmod = llvm.parse_assembly(str(module))
  pm.run(llmod)

  # Mapping llvm value back to our ir
  ll2ir = {}
  # The new dag
  new_dag = {}
  new_root = None

  [f] = list(llmod.functions)
  for arg, x in zip(f.arguments, live_ins):
    val_id = len(ll2ir)
    ll2ir[str(arg)] = val_id
    new_dag[val_id] = x

  [bb] = list(f.blocks)
  for inst in bb.instructions:
    if str(inst.opcode) == 'ret':
      [ret_val] = list(inst.operands)
      new_root = ll2ir[str(ret_val)]
      break

    op = parse_llvm_opcode(inst)
    bitwidth = parse_llvm_bitwidth(inst.type)
    args = [parse_llvm_arg(ll2ir, new_dag, arg) for arg in inst.operands]
    node = Instruction(op, bitwidth, args)
    val_id = len(ll2ir)
    ll2ir[str(inst)] = val_id
    new_dag[val_id] = node

  assert new_root is not None
  return new_dag, new_root

if __name__ == '__main__':
  from pprint import pprint
  import pickle

  debug = '_mm_avg_epu16'
  debug = '_mm256_and_pd'
  debug = '_mm_adds_epi16'
  debug = '_mm_packs_epi32'
  with open('alu.lifted', 'rb') as f:
    lifted = pickle.load(f)
  _, outs, dag = lifted[debug]
  pprint(dag)
  print('===========================')
  new_dag, new_root = canonicalize(dag, outs[0])
  pprint(new_dag)
  print(new_root)
