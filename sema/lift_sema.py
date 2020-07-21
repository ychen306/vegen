'''
Lift smt formula to an IR similar to LLVM (minus control flow)
'''

from collections import namedtuple, defaultdict
import z3_utils
import z3
import bisect
import functools
import operator
import math
from ir import *

def trunc(x, size):
  return Instruction(op='Trunc', bitwidth=size, args=[x])

bitwidth_table = [1, 8, 16, 32, 64]

def get_size(x):
  try:
    return x.bitwidth
  except:
    return x.size()

def quantize_bitwidth(bw):
  idx = bisect.bisect_left(bitwidth_table, bw)
  assert idx < len(bitwidth_table), "bitwidth too large for scalar operation"
  return bitwidth_table[idx]

def trunc_zero(x):
  '''
  truncate all known zero bits from x
  '''
  args = x.children()

  # match a `concat 0, x1`
  if (z3.is_app_of(x, z3.Z3_OP_CONCAT) and
      len(args) == 2 and
      z3.is_bv_value(args[0]) and
      args[0].as_long() == 0):
    return args[1]

  # match const
  if z3.is_bv_value(x):
    size = len(bin(x.as_long()))-2
    return z3.BitVecVal(x.as_long(), size)

  return x

def get_ctrl_key(f, ctrl):
  '''
  check if f is an `if` matching on ctrl
  return the constant being matched if yes
  return None otherwise
  '''
  if not z3.is_app_of(f, z3.Z3_OP_ITE):
    return None

  cond, _, _ = f.children()
  if not z3.is_app_of(cond, z3.Z3_OP_EQ):
    return None

  ctrl2, key = cond.children()
  if z3_utils.askey(ctrl2) != z3_utils.askey(ctrl):
    return None

  if not z3.is_bv_value(key):
    return None

  return key.as_long()

def is_var(x):
  return (z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED) and
      len(x.children()) == 0)

def match_mux(f):
  '''
  turn (if x==0 ... else (if x == 1 ... else (if x == 2  ...))) into a mux
  '''
  if not z3.is_app_of(f, z3.Z3_OP_ITE):
    return None

  cond, _, _ = f.children()
  if not z3.is_app_of(cond, z3.Z3_OP_EQ):
    return None

  ctrl, _ = cond.children()
  if not is_var(ctrl) and not (
      z3.is_app_of(ctrl, z3.Z3_OP_EXTRACT) and is_simple_extraction(ctrl)):
    return None

  mux = {} 
  s = z3.Solver()
  while True:
    key = get_ctrl_key(f, ctrl)
    if key is None:
      if s.check() == z3.unsat:
        # this is a dead branch => we have exhaustively matched everything!
        break

      # try to prove that this is a implicit branch 
      # (i.e., when we get here the key has to be a certain value)
      implicit_key = z3.BitVec('implicit_key', ctrl.size())
      solver_stat = s.check(ctrl == implicit_key)
      if solver_stat == z3.sat:
        # see if there's another key not matched
        key = s.model().eval(implicit_key).as_long()
        s.add(implicit_key != key)
        if s.check(ctrl == implicit_key) != z3.unsat:
          # got to the end of the trail but still didn't exhaust,
          # bail!
          return None
        mux[key] = f
        break

      return None

    cond, a, b = f.children()
    mux[key] = a
    # follow the else branch
    f = b
    s.add(z3.Not(cond))

  return mux, ctrl

class MatchFailure(Exception):
  pass

def match_with(f, op, num_args):
  if not z3.is_app_of(f, op):
    raise MatchFailure
  if len(f.children()) != num_args:
    raise MatchFailure
  return f.children()

def assert_const(f, const):
  if z3.is_bv_value(f) and f.as_long() == const:
    return 
  raise MatchFailure

def assert_pred(pred):
  if not pred:
    raise MatchFailure

def match_insert(f):
  '''
  z3 canonicalizes vector insertion (`src[i] = x`) into the following form:
    keep | update
  where 
    keep = ~(~<src> | <mask of x_size> << <offset>)
    update = x << <offset>
  where
    offset = (<x_size> * <idx>)
  '''
  try:
    s = z3.Solver()
    [keep, update] = match_with(f, z3.Z3_OP_BOR, 2)

    [x, offset1] = match_with(update, z3.Z3_OP_BSHL, 2)
    offset1 = trunc_zero(offset1)
    x = trunc_zero(x)

    [keep] = match_with(keep, z3.Z3_OP_BNOT, 1)
    [not_of_src, mask] = match_with(keep, z3.Z3_OP_BOR, 2)
    [src] = match_with(not_of_src, z3.Z3_OP_BNOT, 1)
    [ones, offset2] = match_with(mask, z3.Z3_OP_BSHL, 2)
    offset2 = trunc_zero(offset2)
    assert_const(ones, (1 << x.size())-1)

    assert_pred(s.check(offset1 != offset2) == z3.unsat)
    [x_size, idx] = match_with(offset1, z3.Z3_OP_BMUL, 2)
    idx = trunc_zero(idx)
    assert_const(x_size, x.size())
    return src, x, idx
  except MatchFailure:
    return None

def match_dynamic_slice(f):
  '''
  z3 doesn't support Extract with dynamic parameters,
  so we compile the semantics of `a[i*stride:(i+1)*stride]` into `trunc(a >> (stride*i))`
  '''
  if not z3.is_app_of(f, z3.Z3_OP_EXTRACT):
    return None

  hi, lo = f.params()
  if lo != 0:
    return None

  [x] = f.children()
  if not z3.is_app_of(x, z3.Z3_OP_BLSHR):
    return None

  base, offset = x.children()
  offset = trunc_zero(offset)
  if not z3.is_app_of(offset, z3.Z3_OP_BMUL):
    return None
  if not is_var(base):
    return None

  stride, idx = offset.children()
  idx = trunc_zero(idx)
  if not z3.is_bv_value(stride):
    return None

  if stride.as_long() != hi + 1:
    return None

  return base, idx, stride.as_long()

def elim_dead_branches(f):
  '''
  remove provably dead branches in z3.If
  '''
  s = z3.Solver()

  cache = {}
  def memoize(elim):
    def wrapped(f):
      key = z3_utils.askey(f)
      if key in cache:
        return cache[key]
      new_f = elim(f)
      cache[key] = new_f
      return new_f
    return wrapped

  @memoize
  def elim(f):
    if z3.is_app_of(f, z3.Z3_OP_ITE):
      cond, a, b = f.children()
      always_true = s.check(z3.Not(cond)) == z3.unsat
      if always_true:
        return elim(a)
      always_false = s.check(cond) == z3.unsat
      if always_false:
        return elim(b)

      cond2 = elim(cond)

      # can't statically determine which branch, follow both!
      # 1) follow the true branch
      s.push()
      s.add(cond)
      a2 = elim(a)
      s.pop()

      # 2) follow the false branch
      s.push()
      s.add(z3.Not(cond))
      b2 = elim(b)
      s.pop()

      return z3.simplify(z3.If(cond2, a2, b2))
    else:
      args = f.children()
      new_args = [elim(arg) for arg in args]
      return z3.simplify(z3.substitute(f, *zip(args, new_args)))

  return elim(f)

def reduce_bitwidth(f):
  '''
  for a formula that looks like `f = op concat(0, a), concat(0, b)`
  try to convert it to `f = concat(0, (op conat(0, a), concat(0, b))`
  so that the inner concat (e.g., zext) is smaller

  do this similarly for `f = op concat(0, a), const`, where const
  has unnecessarily large bitwidth
  '''
  # mapping f -> bitwidth-reduced f
  reduced = {}

  def memoize(reducer):
    def wrapped(f):
      key = z3_utils.askey(f)
      if key in reduced:
        return reduced[key]
      f_reduced = reducer(f)
      reduced[key] = f_reduced
      return f_reduced
    return wrapped

  @memoize
  def reduce_bitwidth_rec(f):
    key = z3_utils.askey(f)
    if key in reduced:
      return reduced[key]

    op = z3_utils.get_z3_app(f)
    # attempt to recursively reduce the bitwidth of sub computation
    new_args = [reduce_bitwidth_rec(arg) for arg in f.children()]

    if op not in alu_op_constructor:
      return z3.simplify(z3.substitute(f, *zip(f.children(), new_args)))

    is_unsigned = True
    pre_zext_args = [trunc_zero(x) for x in new_args]
    if op == z3.Z3_OP_BADD:
      required_bits = max(x.size() for x in pre_zext_args) + len(new_args) - 1
    elif op == z3.Z3_OP_BMUL:
      required_bits = sum(x.size() for x in pre_zext_args)
    elif op in (z3.Z3_OP_BUDIV, z3.Z3_OP_BUDIV_I):
      required_bits = sum(x.size() for x in pre_zext_args)
    elif op == z3.Z3_OP_BLSHR:
      required_bits = pre_zext_args[0].size()
    elif op == z3.Z3_OP_BSHL:
      required_bits = f.size()
    elif op in (z3.Z3_OP_BUREM, z3.Z3_OP_BUREM_I):
      required_bits = pre_zext_args[0].size()
    else:
      # FIXME: also handle signed operation
      # give up
      return z3.simplify(f.decl()(*new_args))
    
    if is_unsigned:
      required_bits = max(required_bits, max(x.size() for x in pre_zext_args))
      zext_args = [
          z3.ZeroExt(required_bits-x.size(), x)
          for x in pre_zext_args
          ]
      f_reduced = alu_op_constructor[op](*zext_args)
      if f_reduced.size() > f.size(): # give up
        return z3.simplify(alu_op_constructor[op](*new_args))
      return z3.simplify(z3.ZeroExt(f.size()-f_reduced.size(), f_reduced))

  return reduce_bitwidth_rec(f)

def typecheck(dag):
  '''
  * make sure the bitwidths match up
  * bitwidths are scalar bitwidth (e.g., 64)
  '''
  for value in dag.values():
    assert type(value) in ir_types
    if isinstance(value, Instruction):
      if value.op in binary_ops:
        args = [dag[arg] for arg in value.args]
        ok = (all(x.bitwidth == args[0].bitwidth for x in args) and
            args[0].bitwidth == value.bitwidth)
      elif value.op in cmp_ops:
        a, b = [dag[arg] for arg in value.args]
        ok = (a.bitwidth == b.bitwidth and value.bitwidth == 1)
      elif value.op == 'Select':
        k, a, b = [dag[arg] for arg in value.args]
        ok = (k.bitwidth == 1 and a.bitwidth == b.bitwidth == value.bitwidth)
      else:
        assert value.op in ['ZExt', 'SExt', 'Trunc']
        ok = True
      if not ok:
        #pprint(value)
        #pprint(dag)
        return False
  return True

def reduction(op, ident):
  return lambda *xs: functools.reduce(op, xs, ident)

alu_op_constructor = {
    z3.Z3_OP_BADD : reduction(operator.add, ident=0),
    z3.Z3_OP_BMUL : reduction(operator.mul, ident=1),
    z3.Z3_OP_BUDIV : z3.UDiv,
    z3.Z3_OP_BUREM : z3.URem,
    z3.Z3_OP_BLSHR : z3.LShR,
    z3.Z3_OP_BSHL : operator.lshift,

    z3.Z3_OP_BSDIV : lambda a, b: a/b,
    
    z3.Z3_OP_BSMOD : operator.mod,
    z3.Z3_OP_BASHR : operator.rshift,
    z3.Z3_OP_BSUB : operator.sub,

    z3.Z3_OP_BSDIV_I: lambda a, b: a/b,
    z3.Z3_OP_BUDIV_I: z3.UDiv,

    z3.Z3_OP_BUREM_I: z3.URem,
    z3.Z3_OP_BSMOD_I: operator.mod,
    }

op_table = {
    z3.Z3_OP_AND: 'And',
    z3.Z3_OP_OR: 'Or',
    z3.Z3_OP_XOR: 'Xor',
    #z3.Z3_OP_FALSE
    #z3.Z3_OP_TRUE
    z3.Z3_OP_ITE: 'Select',
    z3.Z3_OP_BAND : 'And',
    z3.Z3_OP_BOR : 'Or',
    z3.Z3_OP_BXOR : 'Xor',
    z3.Z3_OP_SIGN_EXT: 'SExt',
    z3.Z3_OP_ZERO_EXT: 'ZExt',
    #z3.Z3_OP_BNOT
    #z3.Z3_OP_BNEG
    #z3.Z3_OP_CONCAT
    z3.Z3_OP_ULT : 'Ult',
    z3.Z3_OP_ULEQ : 'Ule',
    z3.Z3_OP_SLT : 'Slt',
    z3.Z3_OP_SLEQ : 'Sle',
    z3.Z3_OP_UGT : 'Ugt',
    z3.Z3_OP_UGEQ : 'Uge',
    z3.Z3_OP_SGT : 'Sgt',

    z3.Z3_OP_SGEQ : 'Sge',
    z3.Z3_OP_BADD : 'Add',
    z3.Z3_OP_BMUL : 'Mul',
    z3.Z3_OP_BUDIV : 'UDiv',
    z3.Z3_OP_BSDIV : 'SDiv',
    z3.Z3_OP_BUREM : 'URem', 
    #z3.Z3_OP_BSREM
    z3.Z3_OP_BSMOD : 'SRem',
    z3.Z3_OP_BSHL : 'Shl',
    z3.Z3_OP_BLSHR : 'LShr',
    z3.Z3_OP_BASHR : 'AShr',
    z3.Z3_OP_BSUB : 'Sub',
    z3.Z3_OP_EQ : 'Eq',

    z3.Z3_OP_DISTINCT : 'Ne',

    z3.Z3_OP_BSDIV_I:  'SDiv',
    z3.Z3_OP_BUDIV_I:  'UDiv',
    #z3.Z3_OP_BSREM_I
    z3.Z3_OP_BUREM_I:  'URem',
    z3.Z3_OP_BSMOD_I:  'SRem',
    }

# translation table from uninterp. func to our ir (basically LLVM)
float_ops = {
    'add': 'FAdd',
    'sub': 'FSub',
    'mul': 'FMul',
    'div': 'FDiv',
    'lt': 'Folt',
    'le': 'Fole',
    'gt': 'Fogt',
    'ge': 'Foge',
    'ne': 'Fone',
    }

def is_simple_extraction(ext):
  '''
  check if `ext` is an extract on a variable
  '''
  [x] = ext.children()
  return (
      z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED) and
      len(x.children()) == 0)

def partition_slices(slices):
  partition = set()
  for s in slices:
    for s2 in partition:
      if s.overlaps(s2):
        partition.remove(s2)
        partition.add(s.union(s2))
        break
    else:
      partition.add(s)
  return partition

class ExtractionHistory:
  '''
  this class records all of the extraction
  done on a set of live-in bitvector,
  '''
  def __init__(self):
    # list of extracted slices
    self.extracted_slices = defaultdict(list)
    self.id_counter = 0

  def record(self, ext):
    assert is_simple_extraction(ext)
    [x] = ext.children()
    hi, lo = ext.params()
    s = Slice(x, lo, hi+1)
    self.extracted_slices[x].append(s)
    return s

  def translate_slices(self, translator):
    '''
    return a map <slice> -> <ir>
    '''
    translated = {}
    for slices in self.extracted_slices.values():
      partition = partition_slices(slices)
      for s in slices:
        for root_slice in partition:
          if s.overlaps(root_slice):
            lo = s.lo - root_slice.lo
            hi = s.hi - root_slice.lo
            assert root_slice.size() >= s.size()
            if s == root_slice:
              translated[s] = root_slice
            elif lo == 0:
              # truncation
              translated[s] = trunc(
                  translator.translate(root_slice.to_z3()),
                  s.size())
            else: # lo > 0
              # shift right + truncation
              #shift = Instruction(
              #    op='LShr',
              #    bitwidth=root_slice.size(),
              #    args=[root_slice])
              #translated[s] = trunc(shift, s.size())
              shift = translator.translate(z3.LShR(root_slice.to_z3(), lo))
              translated[s] = trunc(shift, s.size())
            break
    return translated

def recover_sub(f):
  '''
  z3 simplifies `a + b` to `a + 0b111..11 * b`,
  but we want to turn this into subtraction
  '''
  if not z3.is_app_of(f, z3.Z3_OP_BADD):
    return f
  args = f.children()
  if len(args) != 2:
    return f
  a, b = args
  if not z3.is_app_of(b, z3.Z3_OP_BMUL):
    if z3.is_app_of(a, z3.Z3_OP_BMUL):
      b, a = a, b
    else:
      return f
  b_args = b.children()
  if len(b_args) != 2:
    return f
  b1, b2 = b_args
  if z3.is_true(z3.simplify(b1 == z3.BitVecVal(-1, b1.size()))):
    return a - b2
  return f

def count_reachable_vars(ir, root):
  vars = set()
  visited = set()
  def visit(v):
    if v in visited:
      return
    visited.add(v)
    if isinstance(ir[v], Slice):
      vars.add(ir[v])
      return
    if isinstance(ir[v], Instruction):
      for w in ir[v].args:
        visit(w)
  visit(root)
  return len(vars)

class Translator:
  def __init__(self):
    self.extraction_history = ExtractionHistory()
    self.z3op_translators = {
        z3.Z3_OP_TRUE: self.translate_true, 
        z3.Z3_OP_FALSE: self.translate_false,
        z3.Z3_OP_NOT: self.translate_bool_not,
        z3.Z3_OP_BNOT: self.translate_not,
        z3.Z3_OP_BNEG: self.translate_neg,
        z3.Z3_OP_EXTRACT: self.translate_extract,
        z3.Z3_OP_CONCAT: self.translate_concat,
        z3.Z3_OP_UNINTERPRETED: self.translate_uninterpreted,
        z3.Z3_OP_BNUM: self.translate_constant,
        }
    # mapping <formula> -> <ir node id>
    self.translated = {}
    # translated IR
    self.ir = {}
    self.id_counter = 0

  def new_id(self):
    new_id = self.id_counter
    self.id_counter += 1
    return new_id

  def translate_constant(self, c):
    return Constant(value=c.as_long(), bitwidth=quantize_bitwidth(c.size()))

  def translate_formula(self, f):
    '''
    entry point
    '''
    if not z3.is_app_of(f, z3.Z3_OP_CONCAT):
      outs = [self.translate(f)]
    else:
      elems = f.children()
      sizes = [x.size() for x in elems]
      if len(set(sizes)) != 1:
        # if the sizes are not uniform,
        # partition them so that they are uniform
        size = functools.reduce(math.gcd, sizes)
        partitioned_elems = []
        for x in elems:
          if x.size() == size:
            partitioned_elems.append(x)
            continue
          partitioned_elems.extend(
              z3.simplify(z3.Extract(i+size-1, i, x))
              for i in range(0, x.size(), size))
        elems = partitioned_elems

      # output is a concat, probably vector code
      outs = [self.translate(x) for x in elems]
    # translate the slices
    slice2ir = self.extraction_history.translate_slices(self)
    for node_id, node in self.ir.items():
      if isinstance(node, Slice):
        self.ir[node_id] = slice2ir[node]

    assert all(y in self.ir for y in outs)
    return outs, self.ir

  def translate(self, f):
    # detect `~(a | b)` and turn them into `~a & ~b`
    try:
      [x] = match_with(f, z3.Z3_OP_BNOT, 1)
      [a, b] = match_with(x, z3.Z3_OP_BOR, 2)
      # don't simplify the whole expression
      f = z3.simplify(~a) & z3.simplify(~b)
    except MatchFailure:
      pass

    if f in self.translated:
      return self.translated[f]
    f = recover_sub(f)
    node_id = self.new_id()
    z3op = z3_utils.get_z3_app(f)


    # try to match this to a mux
    insert = match_insert(f)
    # try to match this to a vector insertion
    mux = match_mux(f)

    if insert:
      src, x, idx = insert
      node = Insert(self.translate(src), src.size(),
          self.translate(x), self.translate(idx))
    elif mux is not None:
      mux, ctrl = mux
      keys = list(mux.keys())
      values = [self.translate(mux[k]) for k in keys]
      bitwidth = mux[keys[0]].size()
      assert all(v.size() == bitwidth for v in mux.values())
      node = Mux(
          self.translate(ctrl), 
          keys=keys, values=values,
          bitwidth=bitwidth)
    elif z3op in self.z3op_translators:
      # see if there's a specialized translator
      node = self.z3op_translators[z3op](f)
    else:
      op = op_table[z3op]
      assert z3.is_bv(f) or z3.is_bool(f)
      bitwidth = f.size() if z3.is_bv(f) else 1
      node = Instruction(
          op=op, bitwidth=quantize_bitwidth(bitwidth), 
          args=[self.translate(arg) for arg in f.children()])

    self.translated[f] = node_id
    self.ir[node_id] = node
    return node_id

  def translate_true(*_):
    return Constant(z3.BitVecVal(1, 1))
  
  def translate_false(*_):
    return Constant(z3.BitVecVal(0, 1))

  def translate_bool_not(self, f):
    [x] = f.children()
    return Instruction(
        op='Xor',
        bitwidth=1,
        args=[
          self.translate(z3.BitVecVal(1,1)),
          self.translate(x)])
  
  def translate_not(self, f):
    [x] = f.children()
    # not x == xor -1, x
    node_id = self.translate((-1) ^ x)
    return self.ir[node_id]
  
  def translate_neg(self, f):
    [x] = f.children()
    # not x == sub 0, x
    node_id = self.translate(0-x)
    return self.ir[node_id]
  
  def translate_extract(self, ext):
    if is_simple_extraction(ext):
      s = self.extraction_history.record(ext)
      return s

    s = match_dynamic_slice(ext)
    if s is not None:
      base, idx, stride = s
      assert (z3.is_app_of(idx, z3.Z3_OP_UNINTERPRETED) and 
          len(idx.children()) == 0) or (
          z3.is_app_of(idx, z3.Z3_OP_EXTRACT) and is_simple_extraction(idx))
      return DynamicSlice(base, idx=self.translate(idx), stride=stride)

    [x] = ext.children()
    assert x.size() <= 64,\
        "extraction too complex to model in scalar code"

    _, lo = ext.params()
    if lo > 0:
      return trunc(self.translate(z3.LShR(x, lo)), ext.size())
    return trunc(self.translate(x), ext.size())

  def try_translate_sext(self, concat):
    '''
    don't even bother trying to pattern match this...
    just prove it
    '''
    s = z3.Solver()
    x = concat.children()[-1]
    sext = z3.SignExt(concat.size()-x.size(), x)
    is_sext = s.check(concat != sext) == z3.unsat
    if is_sext:
      return Instruction(
          op='SExt', 
          bitwidth=quantize_bitwidth(concat.size()),
          args=[self.translate(x)])
    return None

  def translate_concat(self, concat):
    '''
    try to convert concat of sign bit to sext
    '''
    sext = self.try_translate_sext(concat)
    if sext is not None:
      return sext

    args = concat.children()
    assert len(args) == 2, "only support using concat for zext"
    a, b = args
    assert z3.is_bv_value(a) and a.as_long() == 0,\
        "only support using concat for zero extension"

    b_translated = self.translate(b)
    # there's a chance that we already upgraded the bitwidth of b
    # during translation (e.g. b.size = 17 and we normalize to 32)
    concat_size = quantize_bitwidth(concat.size())
    if self.ir[b_translated].bitwidth == concat_size:
      return self.ir[b_translated]
    return Instruction(
        op='ZExt', 
        bitwidth=concat_size, args=[b_translated])

  def translate_saturation(self, f):
    sat_name = f.decl().name()
    [x] = f.children()

    _, in_name, _, out_name = sat_name.split('_')

    in_signed = in_name.startswith('s')
    in_bw = int(in_name[1:])

    out_signed = out_name.startswith('s')
    out_bw = int(out_name[1:])

    saturated = z3_utils.saturate(x, in_bw, in_signed, out_bw, out_signed)
    node_id = self.translate(z3.Extract(f.size()-1, 0, saturated))
    return self.ir[node_id]

  def translate_uninterpreted(self, f):
    args = f.children()
    if len(args) == 0:
      # live-in
      return self.extraction_history.record(z3.Extract(f.size()-1, 0, f))

    func = f.decl().name()

    if func.startswith('Saturate'):
      return self.translate_saturation(f)

    assert func.startswith('fp_')
    _, op, _ = func.split('_')
    assert z3.is_bool(f) or f.size() in [32, 64]
    bitwidth = 1 if z3.is_bool(f) else f.size()
    if op == 'neg':
      # implement `neg x` as `fsub 0, x`
      [x] = f.children()
      zero = z3.BitVecVal(0, x.size())
      return Instruction(
          op='FSub', bitwidth=bitwidth,
          args=[self.translate(zero), self.translate(x)])

    return Instruction(
        op=float_ops[op], bitwidth=bitwidth,
        args=[self.translate(arg) for arg in f.children()])

def is_alu_op(dag):
  return any(isinstance(v, Instruction) for v in dag.values())

if __name__ == '__main__':
  from semas import semas
  from pprint import pprint
  from tqdm import tqdm
  import traceback
  import math
  import functools
  import pickle

  debug = '_mm_dpwssds_epi32'
  debug = '_mm256_andnot_pd'
  debug = '_mm_packs_epi32'
  debug = '_mm256_min_epu16'
  debug = '_mm256_min_ps'
  if debug:
    translator = Translator()
    y = semas[debug][1][0]
    print('!!1', y)
    y = elim_dead_branches(y)
    y_reduced = reduce_bitwidth(y)
    z3.prove(y_reduced == y)
    y = y_reduced
    outs, dag = translator.translate_formula(y)
    print('typechecked:', typecheck(dag))
    print(outs)
    pprint(dag)
    exit()

  var_counts = []

  log_alu = open('alu.lifted.log', 'w')
  log_shuf = open('shuf.lifted.log', 'w')

  lifted_alu = {}
  lifted_shuf = {}

  s = z3.Solver()

  pbar = tqdm(iter(semas.items()), total=len(semas))
  num_tried = 0
  num_translated = 0
  for inst, sema in pbar:
    num_tried += 1

    translator = Translator()
    xs, ys = sema
    liveins = [x.decl().name() for x in xs]
    y = ys[0]
    y = elim_dead_branches(y)
    y_reduced = reduce_bitwidth(y)
    y = y_reduced

    # compute stat. for average number of variables
    try:
      outs, dag = translator.translate_formula(y)
      assert typecheck(dag)
      num_translated += 1
      sizes = {get_size(dag[y]) for y in outs}
      if len(sizes) != 1:
        gcd = functools.reduce(math.gcd, sizes)
        print(inst, gcd, gcd in sizes)
      if is_alu_op(dag):
        log_alu.write(inst+'\n')
        lifted_alu[inst] = liveins, outs, dag
      else:
        log_shuf.write(inst+'\n')
        lifted_shuf[inst] = liveins, outs, dag
    except Exception as e:
      #if not isinstance(e, AssertionError):
      #  print('Error processing', inst)
      #  traceback.print_exc()
      #  exit()
      print(inst)
      #print('ERROR PROCESSING:', inst)
      #traceback.print_exc()
    pbar.set_description('translated/tried: %d/%d' % (
      num_translated, num_tried))

  with open('alu.lifted', 'wb') as f:
    pickle.dump(lifted_alu, f)
  with open('shuf.lifted', 'wb') as f:
    pickle.dump(lifted_shuf, f)
