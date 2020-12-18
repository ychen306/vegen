import fp_sema
import sys
import json
from collections import namedtuple
import re
import operator
from z3_utils import *

VectorType = namedtuple('VectorType', ['elem_size', 'num_elems', 'is_signed', 'is_float'])

semas = {}

type_re = re.compile('[a-z]*(\d+)x(\d+)_t')
def parse_vector_type(typename):
  '''
  E.g., int32x8_t -> (32, 8)
  '''
  matched = type_re.match(typename)
  return VectorType(int(matched.group(1)),
      int(matched.group(2)), not typename.startswith('u'), typename.startswith('float'))

counter = 0
def gen_name():
  global counter
  counter += 1
  return 'tmp%d' % counter

# declare a new Z3 symbolic value
def new_sym_val(bw):
  return z3.BitVec(gen_name(), bw)

def split_vector(x, stride):
  return [z3.Extract(i * stride + stride - 1, i * stride, x)
      for i in range(x.size() // stride)]

intrin_re = re.compile(r'[a-z0-9_]+\s*([a-z0-9_]+)\(.*')
def get_intrin_name(sig):
  return intrin_re.match(sig).group(1)

def concat(xs):
  if len(xs) == 1:
    return xs[0]
  return z3.Concat(*xs)

def gen_simd(eval_ty, sig):
  vec_types = [parse_vector_type(arg.split()[0])
      for arg in sig[sig.index('(')+1:sig.index(')')].split(',')]
  elem_size, _, is_signed, is_float = parse_vector_type(sig.strip().split()[0])
  evaluator = eval_ty(is_signed, is_float)
  vecs = [new_sym_val(elem_size * num_elems) for elem_size, num_elems, _, _ in vec_types]
  # wtf is this
  y = [z3.Extract(elem_size-1, 0, evaluator.run(x))
      for x in zip(*(split_vector(vec, elem_size)
    for vec, (elem_size, _, _, _) in zip(vecs, vec_types)
    ))]
  return vecs, z3.simplify(concat(list(reversed(y))))

def round_bitwidth(bw):
  if bw <= 8:
    return 8
  if bw <= 16:
    return 16
  if bw <= 32:
    return 32
  if bw <= 64:
    return 64
  if bw <= 128:
    return 128
  return bw

class Evaluator:
  def __init__(self, is_signed, is_float):
    self.is_float = is_float
    self.is_signed = is_signed

  def run(self, args):
    raise NotImplemented

  def add(self, a, b):
    if self.is_float:
      return fp_sema.binary_float_op('add', True)(a, b)[0]
    bw = round_bitwidth(max(a.size(), b.size()) + 1)
    return fix_bitwidth(a, bw, self.is_signed) + fix_bitwidth(b, bw, self.is_signed)

  def sub(self, a, b):
    if self.is_float:
      return fp_sema.binary_float_op('sub', True)(a, b)[0]
    bw = round_bitwidth(max(a.size(), b.size()) + 1)
    return fix_bitwidth(a, bw, self.is_signed) - fix_bitwidth(b, bw, self.is_signed)

  def mul(self, a, b):
    if self.is_float:
      return fp_sema.binary_float_op('mul', True)(a, b)[0]
    bw = round_bitwidth(a.size() + b.size())
    return fix_bitwidth(a, bw, self.is_signed) * fix_bitwidth(b, bw, self.is_signed)

  def shr(self, a, b):
    if self.is_signed:
      return a >> b
    return z3.LShR(a, b)

class Add(Evaluator):
  def run(self, args):
    return self.add(*args)

class HalvingAdd(Evaluator):
  def run(self, args):
    a, b = args
    return self.shr(self.add(a, b), 1)

class RoundingHalvingAdd(Evaluator):
  def run(self, args):
    a, b = args
    return self.shr(self.add(a, b)+1, 1)

class SaturatingAdd(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    saturate = get_saturator(bw * 2, bw, self.is_signed)
    return saturate(self.add(a, b))

class AddHighHalf(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    return z3.Extract(bw-1, bw//2, self.add(a, b))

class RoundingAddHighHalf(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    return z3.Extract(bw-1, bw//2, self.add(a, b) + (1 << (bw//2-1)))

class Mul(Evaluator):
  def run(self, args):
    return self.mul(*args)

class MultiplyAccumulate(Evaluator):
  def run(self, args):
    a, b, c = args
    return self.add(a, self.mul(b, c))

class MultiplySub(Evaluator):
  def run(self, args):
    a, b, c = args
    return self.sub(a, self.mul(b, c))

class SaturatingDoublingMultiplyHigh(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    saturate = get_saturator(bw * 2, bw, self.is_signed)
    return saturate(self.shr(self.mul(a, b) * 2, bw))

class RoundingSaturatingDoublingMultiplyHigh(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    saturate = get_saturator(bw * 2, bw, self.is_signed)
    return saturate(self.shr(self.mul(a, b) * 2 + (1<<(bw-1)), bw))

class Sub(Evaluator):
  def run(self, args):
    return self.sub(*args)

class SaturatingSub(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    saturate = get_saturator(bw * 2, bw, self.is_signed)
    return saturate(self.sub(a, b))

class HalvingSub(Evaluator):
  def run(self, args):
    a, b = args
    return self.shr(self.sub(a, b), 1)

class SubHighHalf(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    return z3.Extract(bw-1, bw//2, self.sub(a, b))

class RoundingSubHighHalf(Evaluator):
  def run(self, args):
    a, b = args
    bw = a.size()
    return z3.Extract(bw-1, bw//2, self.sub(a, b) + (1 << (bw//2-1)))

evaluators = {
    'add': Add,
    'hadd': HalvingAdd,
    'rhadd': RoundingHalvingAdd,
    'qadd': SaturatingAdd,
    'addhn': AddHighHalf,
    'raddhn': RoundingAddHighHalf,
    'mul': Mul,
    'mla': MultiplyAccumulate,
    'mls': MultiplySub,
    'qdmulh': SaturatingDoublingMultiplyHigh,
    'qrdmulh': RoundingSaturatingDoublingMultiplyHigh, # wtf is this
    'sub': Sub,
    'qsub': SaturatingSub,
    'hsub': HalvingSub,
    'subhn': SubHighHalf,
    'rsubhn': RoundingSubHighHalf,
    }

#print(gen_simd(Add, 'int8x8_t    vadd_s8(int8x8_t a, int8x8_t b);         // VADD.I8 d0,d0,d0'))
#print(gen_simd(Add, 'float32x4_t vaddq_f32(float32x4_t a, float32x4_t b); // VADD.F32 q0,q0,q0'))
#print(gen_simd(HalvingAdd, 'int8x8_t   vhadd_s8(int8x8_t a, int8x8_t b);       // VHADD.S8 d0,d0,d0'))
#print(gen_simd(HalvingAdd, 'uint8x8_t   vhadd_u8(uint8x8_t a, uint8x8_t b);       // VHADD.S8 d0,d0,d0'))
#print(gen_simd(SaturatingAdd, 'int16x8_t  vaddw_s8(int16x8_t a, int8x8_t b);     // VADDW.S8 q0,q0,d0'))
#print(gen_simd(SaturatingAdd, 'uint8x16_t vqaddq_u8(uint8x16_t a, uint8x16_t b);  // VQADD.U8 q0,q0,q0 '))
#print(gen_simd(AddHighHalf, "uint8x8_t  vaddhn_u16(uint16x8_t a, uint16x8_t b); // VADDHN.I16 d0,q0,q0"))
#print(gen_simd(RoundingAddHighHalf, "uint8x8_t  vraddhn_u16(uint16x8_t a, uint16x8_t b); // VRADDHN.I16 d0,q0,q0"))
#print(gen_simd(Mul, "float32x2_t vmul_f32(float32x2_t a, float32x2_t b);  // VMUL.F32 d0,d0,d0"))
#print(gen_simd(Mul, "uint8x8_t   vmul_u8(uint8x8_t a, uint8x8_t b);       // VMUL.I8 d0,d0,d0 "))
#print(gen_simd(MultiplyAccumulate, "int8x8_t    vmla_s8(int8x8_t a, int8x8_t b, int8x8_t c);        // VMLA.I8 d0,d0,d0 "))
#print(gen_simd(MultiplyAccumulate, "uint16x8_t vmlal_u8(uint16x8_t a, uint8x8_t b, uint8x8_t c);    // VMLAL.U8 q0,d0,d0 "))

intrinsics_f = sys.argv[1]
with open(intrinsics_f) as f:
  for category, intrinsics in json.load(f).items():
    evaluator_ty = evaluators[category]
    for intrin in intrinsics:
      print(intrin)
      gen_simd(evaluator_ty, intrin)
