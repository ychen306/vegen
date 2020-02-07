import z3
import operator

# TODO: rename this file to z3_utils
def bool2bv(b):
  return z3.If(b, z3.BitVecVal(1,1), z3.BitVecVal(0,1))

uninterpreted_funcs = {}

def get_uninterpreted_func(func_name, param_types):
  if func_name in uninterpreted_funcs:
    return uninterpreted_funcs[func_name]

  func = z3.Function(func_name, *param_types)
  uninterpreted_funcs[func_name] = func
  return func

BV32 = z3.BitVecSort(32)
BV64 = z3.BitVecSort(64)

precise = True

def set_precision(_precise):
  global precise
  precise = _precise

def get_precision():
  return precise

def fp_literal(val, bitwidth):
  if bitwidth == 32:
    ty = z3.Float32()
  else:
    assert bitwidth == 64
    ty = z3.Float64()
  fp = z3.FPVal(val, ty)
  bv = z3.fpToIEEEBV(fp)
  assert(bv.size() == bitwidth)
  return bv

def bv2fp(x):
  '''
  reinterpret x as a float
  '''
  bitwidth = x.size()
  if bitwidth == 32:
    ty = z3.Float32()
  else:
    assert bitwidth == 64
    ty = z3.Float64()
  return z3.fpBVToFP(x, ty)

def binary_float_op(op):
  def impl(a, b, _=None):
    if z3.is_bv(a):
      bitwidth = a.size()
      if not z3.is_bv(b):
        b = fp_literal(b, bitwidth)
    else:
      assert z3.is_bv(b)
      bitwidth = b.size()
      a = fp_literal(a, bitwidth)
    assert bitwidth in (32, 64)
    if bitwidth == 32:
      ty = BV32
    else:
      ty = BV64
    if not precise:
      func_name = 'fp_%s_%d' % (op, bitwidth)
      func = get_uninterpreted_func(func_name, (ty, ty, ty))
      return func(a, b)
    else:
      c = {
          'add': operator.add,
          'sub': operator.sub,
          'mul': operator.mul,
          'div': operator.truediv, }[op](bv2fp(a), bv2fp(b))
      return z3.fpToIEEEBV(c)
  return impl

def binary_float_cmp(op):
  def impl(a, b, _=None):
    assert a.size() == b.size()
    bitwidth = a.size()
    assert bitwidth in (32, 64)
    if bitwidth == 32:
      ty = BV32
    else:
      ty = BV64
    if not precise:
      func_name = 'fp_%s_%d' % (op, bitwidth)
      func = get_uninterpreted_func(func_name, (ty, ty, z3.BoolSort()))
      result = func(a,b)
      assert z3.is_bool(result)
    else:
      result = {
          'lt': operator.lt,
          'le': operator.le,
          'gt': operator.gt,
          'ge': operator.ge,
          'ne': operator.ne,
          }[op](bv2fp(a), bv2fp(b))

    return bool2bv(result)
  return impl

def unary_float_op(op):
  assert op == 'neg'

  def impl(a):
    bitwidth = a.size()
    assert bitwidth in (32, 64)
    if bitwidth == 32:
      ty = BV32
    else:
      ty = BV64
    if not precise:
      func_name = 'fp_%s_%d' % (op, bitwidth)
      func = get_uninterpreted_func(func_name, (ty, ty))
      return func(a)
    else:
      return z3.fpToIEEEBV(-bv2fp(a))
  return impl
