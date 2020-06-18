import operator
import functools
from intrinsic_types import (
    intrinsic_types, max_vl,
    IntegerType, FloatType, DoubleType,
    is_float, is_literal)
from sema_ast import *
from fp_sema import *
import z3
import math

'''
TODO: convert z3.If into masking???
'''

max_unroll_factor = max_vl * 2

def unreachable():
  assert False

minimize_bitwidth = False
def set_bitwidth_minimization(v):
  global minimize_bitwidth
  minimize_bitwidth = v


class Environment:
  def __init__(self, func_defs=None):
    self.vars = {}
    if func_defs is None:
      func_defs = {}
    self.func_defs = func_defs
    # mapping expr -> signess
    self.reconfigured_binary_exprs = {}

  def configure_binary_expr_signedness(self, configs):
    self.reconfigured_binary_exprs = dict(configs)

  def get_binary_expr_signedness(self, expr):
    return self.reconfigured_binary_exprs.get(expr.expr_id, None)

  def new_env(self):
    return Environment(self.func_defs)

  def def_func(self, func, func_def):
    self.func_defs[func] = func_def

  def get_func(self, func):
    return self.func_defs[func]

  def define(self, name, type, value=None):
    assert name not in self.vars
    self.vars[name] = type, value

  def undef(self, name):
    del self.vars[name]

  def has(self, name):
    return name in self.vars

  def get_type(self, name):
    ty, _ = self.vars[name]
    return ty

  def set_type(self, name, ty):
    _, val = self.vars[name]
    self.vars[name] = ty, val

  def get_value(self, name):
    _, val = self.vars[name]
    return val

  def set_value(self, name, value):
    type = self.get_type(name)
    self.vars[name] = type, value

def match_bitwidth(a, b, signed=False):
  if type(a) == int or type(b) == int:
    return a, b
  bitwidth = max(a.size(), b.size())
  if signed:
    a = z3.SignExt(bitwidth-a.size(), a)
    b = z3.SignExt(bitwidth-b.size(), b)
  else:
    a = z3.ZeroExt(bitwidth-a.size(), a)
    b = z3.ZeroExt(bitwidth-b.size(), b)
  return a, b

def fix_bitwidth(x, bitwidth, signed=False):
  if x.size() < bitwidth:
    if signed:
      return z3.SignExt(bitwidth-x.size(), x)
    return z3.ZeroExt(bitwidth-x.size(), x)
  return z3.Extract(bitwidth-1, 0, x)

def is_constant(x):
  return isinstance(x, z3.BitVecNumRef)

def slice_bit_vec(bv, lo, hi):
  lo = z3.simplify(lo)
  hi = z3.simplify(hi)
  if is_constant(lo) and is_constant(hi):
    # turn this into extraction, which is more "simplifier-friendly"
    return z3.Extract(hi.as_long(), lo.as_long(), bv)

  # "slow" path for when lo and hi can't be simplified:
  bitwidth = z3.simplify(z3.ZeroExt(max_vl, z3.simplify(hi - lo+1)))
  if z3.is_bv_value(bitwidth):
    lo = fix_bitwidth(lo, bv.size())
    return fix_bitwidth(z3.Extract(bitwidth.as_long()-1, 0, z3.LShR(bv, lo)), bv.size())

  # worst case: not even size of the extraction is known
  mask = (1 << bitwidth) - 1
  mask = z3.Extract(bv.size()-1, 0, mask)
  lo = fix_bitwidth(lo, bv.size())
  return z3.LShR(bv, lo) & mask

get_total_arg_width = lambda a, b: a.size() + b.size()
get_max_arg_width = lambda a, b: max(a.size(), b.size())
get_add_width = lambda a, b: get_max_arg_width(a, b) + 1
get_left_width = lambda a, _: a.size()

def select_op(op, signed):
  if signed:
    return op

  # mapping signed op -> unsigned counterpart
  unsigned_ops = {
      operator.lt: z3.ULT,
      operator.le: z3.ULE,
      operator.gt: z3.UGT,
      operator.ge: z3.UGE,
      operator.rshift: z3.LShR,
  }
  return unsigned_ops.get(op, op)

def binary_op(op, signed=True, trunc=False, get_bitwidth=lambda a, b:max(a.size(), b.size())):
  def impl(a, b, signed_override=signed):
    bitwidth = get_bitwidth(a, b)
    mask = (1 << get_max_arg_width(a,b))-1
    a = fix_bitwidth(a, bitwidth, signed_override)
    b = fix_bitwidth(b, bitwidth, signed_override)
    c = select_op(op, signed_override)(a, b)
    if trunc:
      c = c & mask
    return c
  return impl

def get_max_shift_width(a, b):
  return max(a.size(), b.size(), max_vl)

# mapping <op, is_float?> -> impl
binary_op_impls = {
    ('+', True): binary_float_op('add'),
    ('-', True): binary_float_op('sub'),
    ('*', True): binary_float_op('mul'),
    ('/', True): binary_float_op('div'),
    ('<', True): binary_float_cmp('lt'),
    ('<=', True): binary_float_cmp('le'),
    ('>', True): binary_float_cmp('gt'),
    ('>=', True): binary_float_cmp('ge'),
    ('!=', True): binary_float_cmp('ne'),
    ('>>', True): binary_op(operator.rshift, signed=False, get_bitwidth=get_left_width),
    ('<<', True): binary_op(operator.lshift, signed=False, get_bitwidth=get_max_shift_width),

    ('AND', True): binary_op(operator.and_, signed=False),
    ('OR', True): binary_op(operator.or_, signed=False),
    ('XOR', True): binary_op(operator.xor, signed=False),

    # FIXME: what about the signednes?????
    ('*', False): binary_op(operator.mul, get_bitwidth=get_total_arg_width, signed=False),
    ('+', False): binary_op(operator.add, get_bitwidth=get_add_width, signed=False),
    ('-', False): binary_op(operator.sub, get_bitwidth=get_add_width, signed=False),
    ('>', False): binary_op(operator.gt),
    ('>=', False): binary_op(operator.ge),
    ('<', False): binary_op(operator.lt),
    ('<=', False): binary_op(operator.le),
    ('%', False): binary_op(operator.mod, signed=True),
    ('<<', False): binary_op(operator.lshift, signed=False, get_bitwidth=get_max_shift_width),
    ('>>', False): binary_op(operator.rshift, signed=False, get_bitwidth=get_left_width),

    ('AND', False): binary_op(operator.and_, signed=False),
    ('&', False): binary_op(operator.and_, signed=False),
    ('|', False): binary_op(operator.or_, signed=False),
    ('OR', False): binary_op(operator.or_, signed=False),
    ('XOR', False): binary_op(operator.xor, signed=False),

    ('!=', False): binary_op(operator.ne),
    }

# mapping <op, is_float?> -> impl
unary_op_impls = {
    ('NOT', True): lambda a: ~a,
    ('-', True): unary_float_op('neg'),

    ('NOT', False): lambda a:~a,
    ('-', False): operator.neg,
    ('~', False): lambda a:~a,
    }

class SymbolicSlice:
  def __init__(self, var, lo_idx, hi_idx, stride=1):
    self.var = var
    self.lo_idx, self.hi_idx = match_bitwidth(lo_idx, hi_idx, signed=False)
    self.zero_extending = True
    self.stride = stride

  def set_stride(self, stride):
    return SymbolicSlice(self.var, self.lo_idx, self.hi_idx, stride)

  def slice(self, lo, hi):
    lo = lo * self.stride
    hi = (hi+1) * self.stride - 1
    bitwidth = max(lo.size(), hi.size())
    lo = fix_bitwidth(lo, bitwidth)
    hi = fix_bitwidth(hi, bitwidth)
    lo_idx = fix_bitwidth(self.lo_idx, bitwidth)
    hi_idx = fix_bitwidth(self.hi_idx, bitwidth)
    return SymbolicSlice(self.var, lo+lo_idx, hi+lo_idx, self.stride)

  def __repr__(self):
    return '%s[%d:%d]' % (self.var, self.lo_idx, self.hi_idx)

  def mark_sign_extend(self):
    self.zero_extending = False

  def update(self, rhs, env, pred):
    '''
    rhs : integer
    '''
    if env.get_value(self.var) is None:
      lo_idx = z3.simplify(self.lo_idx)
      assert is_constant(lo_idx) and lo_idx.as_long() == 0
      env.set_value(self.var, rhs)
      self.hi_idx = rhs.size() - 1
      ty = env.get_type(self.var)
      env.set_type(self.var, ty._replace(bitwidth=rhs.size()))
      return
      
    old_val = env.get_value(self.var)
    bitwidth = old_val.size()

    # fast path for when we can statically determine hi and lo idxs
    lo_idx = z3.simplify(self.lo_idx)
    hi_idx = z3.simplify(self.hi_idx)
    if z3.is_bv_value(lo_idx) and z3.is_bv_value(hi_idx):
      lo = lo_idx.as_long()
      hi = hi_idx.as_long()
      if hi < lo or lo >= bitwidth:
        return
      rhs = fix_bitwidth(rhs, hi-lo+1)
      # old_val = HI MID LO, we update MID
      if hi < bitwidth-1 and lo > 0:
        hi_chunk = z3.Extract(bitwidth-1, hi+1, old_val)
        mid_chunk = z3.If(pred, rhs, z3.Extract(hi, lo, old_val))
        lo_chunk = z3.Extract(lo-1, 0, old_val)
        new_val = z3.Concat(hi_chunk, mid_chunk, lo_chunk)
      elif hi == bitwidth - 1 and lo > 0:
        mid_chunk = z3.If(pred, rhs, z3.Extract(hi, lo, old_val))
        lo_chunk = z3.Extract(lo-1, 0, old_val)
        new_val = z3.Concat(mid_chunk, lo_chunk)
      elif hi < bitwidth-1 and lo == 0:
        hi_chunk = z3.Extract(bitwidth-1, hi+1, old_val)
        mid_chunk = z3.If(pred, rhs, z3.Extract(hi, lo, old_val))
        new_val = z3.Concat(hi_chunk, mid_chunk)
      else:
        assert hi >= bitwidth-1
        assert lo == 0
        new_val = z3.If(pred, rhs, old_val)

      assert new_val.size() == old_val.size()
      env.set_value(self.var, new_val)
      return 

    update_bitwidth = self.hi_idx - self.lo_idx + 1
    # TODO: remove this if
    # increase bitwidth for symbolic bitvector in case of overflow
    if not isinstance(update_bitwidth, int):
      update_bitwidth = z3.ZeroExt(old_val.size(), update_bitwidth)
    mask = (1 << update_bitwidth) - 1
    mask = z3.Extract(bitwidth-1, 0, mask)

    rhs = fix_bitwidth(rhs, bitwidth)
    self.lo_idx = fix_bitwidth(self.lo_idx, bitwidth)
    rhs = (rhs & mask) << self.lo_idx

    new_val = z3.If(pred, (old_val & ~(mask << self.lo_idx)) | rhs, old_val)

    env.set_value(self.var, new_val)

  def get_value(self, env):
    bitwidth = self.hi_idx - self.lo_idx + 1
    total_bitwidth = env.get_type(self.var).bitwidth
    val = slice_bit_vec(env.get_value(self.var), self.lo_idx, self.hi_idx)
    return val

counter = 0
def gen_name():
  global counter
  counter += 1
  return 'tmp%d' % counter

def get_value(slice_or_val, env):
  if isinstance(slice_or_val, SymbolicSlice):
    return slice_or_val.get_value(env)
  return slice_or_val

# declare a new Z3 symbolic value
def new_sym_val(type):
  return z3.BitVec(gen_name(), type.bitwidth)

def conc_val(val, type):
  return z3.BitVecVal(val, type.bitwidth)

def compile_for(for_stmt, env, pred=True):
  # compile the naive way first 
  inc = lambda x: x + 1
  dec = lambda x: x - 1
  next = inc if for_stmt.inc else dec
  begin, _ = compile_expr(for_stmt.begin, env, deref=True)
  end, _ = compile_expr(for_stmt.end, env, deref=True)
  env.define(for_stmt.iterator, type=IntegerType(32), value=begin)

  done = False
  # attempt to fully unroll the loop
  for _ in range(max_unroll_factor):
    it = env.get_value(for_stmt.iterator)
    it, end = match_bitwidth(it, end)
    if for_stmt.inc:
      done = z3.Or(done, it > end)
    else:
      done = z3.Or(done, it < end)
    done = z3.simplify(done)
    if z3.is_true(done):
      break
    for stmt in for_stmt.body:
      compile_stmt(stmt, env, pred=z3.And(z3.Not(done), pred))
    env.set_value(for_stmt.iterator, next(it))

  env.undef(for_stmt.iterator)

def compile_number(n, env, pred):
  if isinstance(n.val, int):
    ty = IntegerType(64)
    val = conc_val(n.val, ty)
    return val, ty
  else:
    return n.val, None # keep it a literal

def compile_update(update, env, pred):
  rhs, rhs_type = compile_expr(update.rhs, env, pred)

  if (type(update.rhs) == Call and
    type(update.rhs.func) == Var and
    update.rhs.func.name == 'SignExtend'):
    sign_extending = True
  else:
    sign_extending = False

  # TODO: refactor this shit out
  if type(update.lhs) == Var and not env.has(update.lhs.name):
    env.define(update.lhs.name, type=rhs_type, value=None)
    assert env.has(update.lhs.name)

  lhs, _ = compile_expr(update.lhs, env, pred)

  # propagate type from RHS
  lhs_type = env.get_type(lhs.var)
  env.set_type(lhs.var, 
      lhs_type._replace(
        is_float=lhs_type.is_float or rhs_type.is_float,
        is_double=lhs_type.is_float or rhs_type.is_double))

  if sign_extending:
    lhs.mark_sign_extend()

  rhs_val = get_value(rhs, env)
  lhs.update(rhs_val, env, pred)
  return rhs_val

def compile_unary_expr(expr, env, pred):
  a, a_type = compile_expr(expr.a, env, pred, deref=True)
  impl_sig = expr.op, is_float(a_type)
  impl = unary_op_impls[impl_sig]
  return impl(a), a_type

def collect_chained_cmpeq(expr, chained):
  if type(expr) != BinaryExpr or expr.op != '==':
    chained.append(expr)
    return
  
  collect_chained_cmpeq(expr.a, chained)
  collect_chained_cmpeq(expr.b, chained)


def compile_binary_expr(expr, env, pred):
  # special case for expression like "a == b == c == d"
  if expr.op == '==':
    chained_operands = []
    collect_chained_cmpeq(expr, chained_operands)
    vals = [compile_expr(operand, env, deref=True) for operand in chained_operands]
    v, _ = vals[0]
    equalities = []
    for v2, _ in vals[1:]:
      v1, v2 = match_bitwidth(v, v2)
      equalities.append(v1 == v2)
    all_equal = z3.And(equalities)
    return bool2bv(all_equal), IntegerType(1)

  a, a_type = compile_expr(expr.a, env, pred, deref=True)
  b, b_type = compile_expr(expr.b, env, pred, deref=True)

  impl_sig = expr.op, is_float(a_type)
  impl = binary_op_impls[impl_sig]
  # check the configuration for whether this expression is signed
  signedness = env.get_binary_expr_signedness(expr)
  if signedness is not None:
    result = impl(a, b, signedness)
  else:
    # if signedness is not specified, just use the default
    result = impl(a, b)

  if a_type is not None:
    ty = a_type
  else:
    ty = b_type
  assert ty is not None
  if z3.is_bool(result):
    result = bool2bv(result)
  return result, ty._replace(bitwidth=result.size())

def compile_var(var, env, pred=True):
  '''
  return a slice/reference, which can be update/deref later
  '''
  if var.name == 'undefined':
    return None, None
  type = env.get_type(var.name)
  slice = SymbolicSlice(var.name, conc_val(0, IntegerType(32)), conc_val(type.bitwidth-1, IntegerType(32)))
  return slice, type

def compile_stmt(stmt, env, pred=True):
  '''
  whether this statement is executed is controlled by the predicate
  '''
  stmt_ty = type(stmt)
  compilers[stmt_ty](stmt, env, pred)

def compile_expr(expr, env, pred=True, deref=False):
  expr_ty = type(expr)
  slice_or_val, ty = compilers[expr_ty](expr, env, pred)
  if deref:
    return get_value(slice_or_val, env), ty
  return slice_or_val, ty

def is_mask(ty):
  return ty.startswith('__mmask')

def compile(spec):
  # bring the arguments into scope
  env = Environment()
  env.configure_binary_expr_signedness(spec.configs)

  out_params = []
  returns_void = False
  param_vals = []
  for param in spec.params:
    is_out_param = False
    if param.type.endswith('*'):
      param_type = intrinsic_types[param.type[:-1].strip()]
      out_params.append(param.name)
      is_out_param = True
    else:
      param_type = intrinsic_types[param.type]
    param_val = new_sym_val(param_type)
    if not is_out_param: 
      param_vals.append(param_val)
    env.define(param.name, type=param_type, value=param_val)

  returns_mask = is_mask(spec.rettype)
  if spec.rettype != 'void':
    rettype = intrinsic_types[spec.rettype]
    # if the environment has 'k' defined. E.g. k is a parameter
    # the k cannot be returned implicitly
    if not returns_mask or env.has('k'):
      env.define('dst', type=rettype, value=new_sym_val(rettype))
    else:
      env.define('k', type=rettype, value=new_sym_val(rettype))
  else:
    returns_void = True

  for stmt in spec.spec:
    if type(stmt) == Return:
      assign_to_dst = Update(lhs=Var('dst'), rhs=stmt.val)
      compile_stmt(assign_to_dst, env)
      break
    compile_stmt(stmt, env)

  outputs = [z3.simplify(env.get_value(out_param)) for out_param in out_params]
  if not returns_void:
    if not returns_mask:
      retval = env.get_value('dst')
    else:
      retval = env.get_value('k')
    out_size = intrinsic_types[spec.rettype].bitwidth
    dst = z3.simplify(fix_bitwidth(retval, out_size), bv_ite2id=True, elim_and=False, elim_ite=False, ite_extra_rules=True)
    outputs = [dst] + outputs
  return param_vals, outputs

def compile_bit_slice(bit_slice, env, pred):
  lo, _ = compile_expr(bit_slice.lo, env, pred, deref=True)

  # special case for the magic variable 'MAX' 
  if (type(bit_slice.hi) == Var and
      bit_slice.hi.name == 'MAX'):
    hi = conc_val(max_vl - 1, IntegerType(32))
  else:
    hi, _ = compile_expr(bit_slice.hi, env, pred, deref=True)

  # in case we have a variable implicitly declared
  # assume only integers can be implicitly declared
  if (type(bit_slice.bv) == Var and
      not env.has(bit_slice.bv.name)):
    env.define(bit_slice.bv.name, type=IntegerType(max_vl), value=conc_val(0, IntegerType(max_vl)))
  slice_src, ty = compile_expr(bit_slice.bv, env, pred)

  # resize bitvectors implicitly defined
  if isinstance(slice_src, SymbolicSlice):
    hi = z3.simplify(hi)
    src = env.get_value(slice_src.var)
    if is_constant(hi) and hi.as_long() >= src.size():
      new_bitwidth = hi.as_long() + 1
      extended = fix_bitwidth(src, new_bitwidth)
      env.set_value(slice_src.var, extended)
      src_ty = env.get_type(slice_src.var)
      env.set_type(
          bit_slice.bv.name, 
          src_ty._replace(bitwidth=new_bitwidth))

  # in case the bits we are slicing from
  #   is a result of a computation, not a variable
  if type(slice_src) != SymbolicSlice:
    return slice_bit_vec(slice_src, lo, hi), ty

  return slice_src.slice(lo, hi), ty

def get_signed_max(bitwidth):
  return (1<<(bitwidth-1))-1

def get_signed_min(bitwidth):
  return -get_signed_max(bitwidth)-1

def get_unsigned_max(bitwidth):
  return (1<<bitwidth)-1

def get_unsigned_min(bitwidth):
  return 0

def gen_saturation_func(bitwidth, in_signed, out_signed):
  hi = get_signed_max(bitwidth) if out_signed else get_unsigned_max(bitwidth)
  lo = get_signed_min(bitwidth) if out_signed else get_unsigned_min(bitwidth)
  def saturate(args, env):
    [(val, _)] = args
    lt = operator.lt if in_signed else z3.ULT
    gt = operator.gt if in_signed else z3.UGT
    new_val = z3.If(
        lt(val, lo),
        lo,
        z3.If(
          gt(val, hi),
          hi,
          val))
    return fix_bitwidth(new_val, bitwidth), IntegerType(bitwidth)
  return saturate

def builtin_concat(args, _):
  # FIXME:
  # this is broken if we can't statically determine the bitwidth of 
  # slicing!!!
  [(a, a_ty), (b, b_ty)] = args
  return z3.Concat(a,b), a_ty._replace(bitwidth=a.size() + b.size())

def builtin_zero_extend(args, env):
  [(val, ty)] = args
  return z3.ZeroExt(max_vl, val), ty

def builtin_sign_extend(args, env):
  [(val, ty)] = args
  return z3.SignExt(max_vl, val), ty

def builtin_abs(args, env):
  [(val, ty)] = args
  if not is_float(ty):
    return z3.If(val < 0, -val, val), ty
  zero = conc_val(0, ty._replace(bitwidth=val.size()))
  lt_0 = binary_float_cmp('lt')(val, zero)
  neg = unary_float_op('neg')(val)
  return z3.If(lt_0 != 0, neg, val), ty


def builtin_binary_func(op):
  def impl(args, _):
    [(a, ty), (b, _)] = args

    if not is_float(ty):
      return Bits(int=op(a.int, b.int), length=ty.bitwidth), ty

    # float
    return Bits(float=op(a.float, b.float), length=ty.bitwidth), ty
  return impl

def builtin_popcount(args, _):
  [(a, _)] = args
  int32 = IntegerType(32)
  bits = [z3.ZeroExt(31, z3.Extract(i,i,a)) for i in range(a.size())]
  zero = conc_val(0, int32)
  count = functools.reduce(operator.add, bits, zero)
  return count, int32 

def builtin_select(args, _):
  '''
  select dword (32-bit) in a[...] by b
  '''
  [(a, a_ty), (b, _)] = args
  b = fix_bitwidth(b, 32)
  bit_idx = b * 32
  selected = slice_bit_vec(a, bit_idx, bit_idx+31)
  return selected, a_ty._replace(bitwidth=32)

builtins = {
    'Saturate_Int16_To_Int8': gen_saturation_func(8, True, True),
    'Saturate_Int16_To_UnsignedInt8': gen_saturation_func(8, True, False),
    'Saturate_Int32_To_Int16': gen_saturation_func(16, True, True),
    'Saturate_Int32_To_Int8': gen_saturation_func(8, True, True),
    'Saturate_Int32_To_UnsignedInt16': gen_saturation_func(16, True, False),
    'Saturate_Int64_To_Int16': gen_saturation_func(16, True, True),
    'Saturate_Int64_To_Int32': gen_saturation_func(32, True, True),
    'Saturate_Int64_To_Int8': gen_saturation_func(8, True, True),
    'Saturate_To_Int16': gen_saturation_func(16, True, True),
    'Saturate_To_Int8': gen_saturation_func(8, True, True),
    'Saturate_To_UnsignedInt16': gen_saturation_func(16, False, False),
    'Saturate_To_UnsignedInt8': gen_saturation_func(8, False, False),
    'Saturate_UnsignedInt16_To_Int8': gen_saturation_func(8, False, True),
    'Saturate_UnsignedInt32_To_Int16': gen_saturation_func(16, False, True),
    'Saturate_UnsignedInt32_To_Int8': gen_saturation_func(8, False, True),
    'Saturate_UnsignedInt64_To_Int16': gen_saturation_func(16, False, True),
    'Saturate_UnsignedInt64_To_Int32': gen_saturation_func(32, False, True),
    'Saturate_UnsignedInt64_To_Int8': gen_saturation_func(8, False, True),
    'SIGNED_DWORD_SATURATE': gen_saturation_func(32, True, True),
    'Truncate_Int32_To_Int8': gen_saturation_func(8, True, True),
    'Truncate_Int64_To_Int8': gen_saturation_func(8, True, True),
    'Truncate_Int32_To_Int16': gen_saturation_func(16, True, True),
    'Truncate_Int64_To_Int32': gen_saturation_func(32, True, True),
    'Truncate_Int64_To_Int16': gen_saturation_func(32, True, True),
    'Truncate_Int16_To_Int8': gen_saturation_func(8, True, True),

    'ZeroExtend': builtin_zero_extend,
    'ZeroExtend_To_512': builtin_zero_extend,
    'ZeroExtend64': builtin_zero_extend,
    'SignExtend': builtin_sign_extend,

    'APPROXIMATE': lambda args, _: args[0], # noop

    'ABS': builtin_abs,
    'concat': builtin_concat,
    'PopCount': builtin_popcount,
    'POPCNT': builtin_popcount,
    'select': builtin_select,
    }

f32_32 = BV32, BV32
f64_32 = BV64, BV32
f32_64 = BV32, BV64
f64_64 = BV64, BV64

def gen_int2fp(in_signed, in_bitwidth, out_bitwidth):
  assert out_bitwidth in (32, 64)
  def precise_impl(x):
    x = fix_bitwidth(x, in_bitwidth)
    if out_bitwidth == 32:
      ty = z3.Float32()
    else:
      ty = z3.Float64()
    if in_singed:
      return z3.fpSignedToFP(z3.RNE(), x, ty)
    return z3.fpUnsignedToFP(z3.RNE(), x, ty), FloatType(out_bitwidth)

  def uninterpreted_impl(x):
    param_types = z3.BitVecSort(in_bitwidth), z3.BitVecSort(out_bitwidth)
    func_name = 'conv_%s%d_to_f%d' % (
        'i' if in_signed else 'u',
        in_bitwidth,
        out_bitwidth)
    func = get_uninterpreted_func(func_name, param_types)
    x = fix_bitwidth(x, in_bitwidth)
    return func(x), FloatType(out_bitwidth)

  return precise_impl if precise else uninterpreted_impl

def gen_fp2int(out_signed, in_bitwidth, out_bitwidth):
  assert in_bitwidth in (32, 64)
  out_ty = z3.BitVecSort(out_bitwidth)
  def precise_impl(x):
    if trunc:
      x = x + 0.5
    x = bv2fp(fix_bitwidth(x, in_bitwidth))
    if out_signed:
      return z3.fpToSBV(z3.RTZ(), x, out_ty)
    return z3.fpToUBV(z3.RTZ(), x, out_ty), IntegerType(out_bitwidth)

  def uninterpreted_impl(x):
    func_name = 'conv_f%d_to_%s_%s%d' % (
        in_bitwidth,
        'i' if out_signed else 'u',
        out_bitwidth)
    if in_bitwidth == 32:
      fp_ty = z3.Float32()
    else:
      fp_ty = z3.Float64()
    param_types = fp_ty, out_ty
    func = get_uninterpreted_func(func_name, param_types)
    return func(x), IntegerType(out_bitwidth)

  return precise_impl if precise else uninterpreted_impl

# mapping func -> type, ret-float?
builtin_convs = {
    'Convert_Int32_To_FP32': gen_int2fp(True, 32, 32),
    'Convert_Int64_To_FP32': gen_int2fp(True, 64, 32),
    'Convert_Int32_To_FP64': gen_int2fp(True, 32, 64),
    'Convert_Int64_To_FP64': gen_int2fp(True, 64, 64),
    'Convert_FP32_To_Int32': gen_fp2int(True, 32, 32),
    'Convert_FP64_To_Int32': gen_fp2int(True, 64, 32),
    'Convert_FP32_To_Int64': gen_fp2int(True, 32, 64),
    'Convert_FP64_To_Int64': gen_fp2int(True, 64, 64),
    'Convert_FP32_To_Int32_Truncate': (f32_32, False),
    'Convert_FP64_To_Int32_Truncate': (f64_32, False),
    'Convert_FP64_To_Int64_Truncate': (f64_64, False),
    'Convert_FP64_To_FP32': (f64_32, True),
    'Convert_FP32_To_FP64': (f32_64, True),
    'Float64ToFloat32': (f64_32, True),
    'Float32ToFloat64': (f32_64, True),
    'Convert_FP64_To_UnsignedInt32': (f64_32, False),
    'Convert_FP32_To_UnsignedInt32': (f64_64, False),
    'Convert_FP64_To_UnsignedInt64': (f64_64, False),
    'Convert_FP32_To_UnsignedInt64': (f32_64, False),
    'Convert_FP64_To_UnsignedInt32_Truncate': (f64_32, False),
    'Convert_FP32_To_UnsignedInt32_Truncate': (f32_32, False),
    'Convert_FP64_To_UnsignedInt64_Truncate': (f64_64, False),
    'Convert_FP32_To_Int64_Truncate': (f32_64, False),
    'Convert_FP32_To_UnsignedInt64_Truncate': (f32_64, False),
    'Convert_FP32_To_IntegerTruncate': (f32_32, False),
    'ConvertUnsignedIntegerTo_FP64': (f32_64, True),
    'ConvertUnsignedInt32_To_FP32': (f32_32, True),
    'Convert_UnsignedInt32_To_FP64': (f32_64, True),
    'Convert_UnsignedInt64_To_FP64': (f64_64, True),
    'Convert_UnsignedInt32_To_FP32': (f32_32, True),
    'Convert_UnsignedInt64_To_FP32': (f64_32, True),
    'ConvertUnsignedInt64_To_FP64': (f64_64, True),
    'ConvertUnsignedInt64_To_FP32': (f64_32, True),
    'Int32ToFloat64': (f32_64, True),
    'UInt32ToFloat64': (f32_64, True),
    }

unary_real_arith = {
    #'SQRT', 'ln'
    }

def is_number(expr):
  return type(expr) == Number

def compile_call(call, env, pred):
  assert type(call.func) == str

  # compute all the arguments
  args = [compile_expr(arg, env, pred, deref=True) for arg in call.args]

  # calling a builtin
  if call.func in builtins:
    # assume builtins don't modify the environment
    return builtins[call.func](args, env)

  if call.func in builtin_convs:
    assert len(args) == 1
    conv_func = builtin_convs[call.func]
    [x] = args
    return conv_func(x)

  # calling funcs like `sqrt', which is could work for either float or double
  if call.func in unary_real_arith:
    [(a, a_ty)] = args
    assert is_float(a_ty) and not is_literal(a_ty)
    bitwidth = a.size()
    assert bitwidth in (32, 64)
    ty = z3.BitVecSort(bitwidth)
    func_name = 'fp_%s_%d' % (call.func.lower(), bitwidth)
    func = get_uninterpreted_func(func_name, (ty, ty))
    return func(a), a_ty

  # assume there is no indirect calls
  func_def = env.get_func(call.func)

  # Calling a user defined function
  # Pass the arguments first
  new_env = env.new_env()
  assert len(func_def.params) == len(args)
  for (arg, arg_type), param in zip(args, func_def.params):
    # make sure the argument bitwidths match 
    if type(param) == BitSlice:
      assert type(param.bv) == Var
      assert is_number(param.lo)
      assert is_number(param.hi)
      assert param.lo.val == 0
      param_name = param.bv.name
      param_width = param.hi.val+1
    else:
      assert type(param) == Var
      param_name = param.name
      param_width = arg.size()
    arg = fix_bitwidth(arg, param_width)
    new_env.define(param_name, arg_type._replace(bitwidth=param_width), arg)

  # step over the function
  for stmt in func_def.body:
    if type(stmt) == Return:
      retval = compile_expr(stmt.val, new_env, pred, deref=True)
      return retval
    compile_stmt(stmt, new_env, pred)

  # user defined function should return explicitly
  unreachable()

def compile_func_def(func_def, env, _):
  env.def_func(func_def.name, func_def)

def compile_if(if_stmt, env, pred):
  cond, _ = compile_expr(if_stmt.cond, env, pred, deref=True)
  yes = cond != 0
  for stmt in if_stmt.then:
    compile_stmt(stmt, env, pred=z3.And(pred, yes))
  for stmt in if_stmt.otherwise:
    compile_stmt(stmt, env, pred=z3.And(pred, z3.Not(yes)))

def compile_select(select, env, pred):
  cond, _ = compile_expr(select.cond, env, pred, deref=True)
  then, then_ty = compile_expr(select.then, env, pred, deref=True)
  otherwise, _ = compile_expr(select.otherwise, env, pred, deref=True)
  return z3.If(cond != 0, then, otherwise), then_ty

def compile_match(match_stmt, env, pred):
  # number of bits required to index the cases
  num_bits = math.ceil(math.log2(len(match_stmt.cases)))
  val_expr = BitSlice(
      match_stmt.val,
      hi=Number(num_bits - 1),
      lo=Number(0))
  val, _ = compile_expr(val_expr, env, pred, deref=True)
  cases = {}
  for case in match_stmt.cases:
    case_val, _ = compile_expr(case.val, env, pred, deref=True)
    case_val, val = match_bitwidth(case_val, val)
    case_matched = (case_val == val)
    for stmt in case.stmts:
      if type(stmt) == Break:
        break
      compile_stmt(stmt, env, pred=z3.And(case_matched, pred))

def prove(predicate):
  s = z3.Solver()
  s.add(z3.Not(predicate))
  return s.check() == z3.unsat

def compile_while(while_stmt, env, pred):
  def keep_going():
    cond, _ = evaluate_expr(while_stmt.cond, env)
    return cond.int

  done = False
  for i in range(max_unroll_factor):
    cond, _ = compile_expr(while_stmt.cond, env, pred, deref=True)
    done = z3.simplify(z3.Or(done, cond == 0))

    # take out the big gun here because sometimes the simplifier doesn't cut it
    if prove(z3.Implies(pred, done)):
      break

    for stmt in while_stmt.body:
      compile_stmt(stmt, env, z3.And(pred, z3.Not(done)))

  assert prove(z3.Implies(pred, done)), "insufficient unroll factor"

def compile_lookup(lookup, env, pred):
  '''
  essentially these expression returns a slice
  whose stride is specified by the property,
  which by defualt is `bit'.

  Some examples:

  a[127:0] is a slice of bits from 0 to 127
  a.byte[0] is a slice of bits from 0 to 7
  a.dword[0].bit[2] is ...
  '''
  if (type(lookup.obj) == Var and
      not env.has(lookup.obj.name)):
    env.define(lookup.obj.name,
        type=IntegerType(max_vl),
        value=new_sym_val(IntegerType(max_vl)))
  strides = {
      'bit': 1,
      'byte': 8,
      'word': 16,
      'dword': 32,
      'qword': 64,
      }
  stride = strides[lookup.key]
  obj, ty = compile_expr(lookup.obj, env)
  return obj.set_stride(stride), ty

compilers = {
    For: compile_for,
    Number: compile_number,
    Update: compile_update,
    BinaryExpr: compile_binary_expr,
    Var: compile_var,
    BitSlice: compile_bit_slice,
    Call: compile_call,
    FuncDef: compile_func_def,
    If: compile_if,
    UnaryExpr: compile_unary_expr,
    Select: compile_select,
    Match: compile_match,
    While: compile_while,
    Lookup: compile_lookup,
    }

if __name__ == '__main__':

  from manual_parser import get_spec_from_xml

  import xml.etree.ElementTree as ET
  sema = '''
<intrinsic tech='AVX' rettype='__m256' name='_mm256_insertf128_ps'>
        <type>Floating Point</type>
        <CPUID>AVX</CPUID>
        <category>Swizzle</category>
        <parameter varname='a' type='__m256'/>
        <parameter varname='b' type='__m128'/>
        <parameter varname="imm8" type='int'/>
        <description>Copy "a" to "dst", then insert 128 bits (composed of 4 packed single-precision (32-bit) floating-point elements) from "b" into "dst" at the location specified by "imm8".</description>
        <operation>
dst[255:0] := a[255:0]
CASE (imm8[1:0]) OF
0: dst[127:0] := b[127:0]
1: dst[255:128] := b[127:0]
ESAC
dst[MAX:256] := 0
        </operation>
        <instruction name='vinsertf128' form='ymm, ymm, xmm, imm'/>
        <header>immintrin.h</header>
</intrinsic>
  '''
  intrin_node = ET.fromstring(sema)
  spec = get_spec_from_xml(intrin_node)
  param_vals, outs = compile(spec)
  print(param_vals, outs)
