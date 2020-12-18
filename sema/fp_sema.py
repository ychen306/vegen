import z3
from z3_utils import get_uninterpreted_func
import operator

# TODO: rename this file to z3_utils
def bool2bv(b):
  return z3.If(b, z3.BitVecVal(1,1), z3.BitVecVal(0,1))

BV32 = z3.BitVecSort(32)
BV64 = z3.BitVecSort(64)

precise = True

def set_precision(_precise):
  global precise
  precise = _precise

def get_precision():
  return precise

def fp_literal(val, bitwidth, use_uninterpreted=False):
  if bitwidth == 32:
    ty = z3.Float32()
  else:
    assert bitwidth == 64
    ty = z3.Float64()

  fp = z3.FPVal(val, ty)
  bv = z3.fpToIEEEBV(fp)
  assert(bv.size() == bitwidth)

  if not precise or use_uninterpreted:
    # mark that this is a fp literal to make lifting easier
    return get_uninterpreted_func('fp_literal_%d' % bitwidth, (bv.sort(), bv.sort()))(bv)

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

def binary_float_op(op, use_uninterpreted=False):
  def impl(a, b, *_):
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
    if not precise or use_uninterpreted:
      func_name = 'fp_%s_%d' % (op, bitwidth)
      func = get_uninterpreted_func(func_name, (ty, ty, ty))
      return func(a, b), bitwidth
    else:
      c = {
          'add': operator.add,
          'sub': operator.sub,
          'mul': operator.mul,
          'div': operator.truediv, }[op](bv2fp(a), bv2fp(b))
      return z3.fpToIEEEBV(c), bitwidth
  return impl

def binary_float_cmp(op, use_uninterpreted=False):
  def impl(a, b, *_):
    assert a.size() == b.size()
    bitwidth = a.size()
    assert bitwidth in (32, 64)
    if bitwidth == 32:
      ty = BV32
    else:
      ty = BV64
    if not precise or use_uninterpreted:
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

    return bool2bv(result), 1
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
