import fp_sema
import sys
from collections import namedtuple
import re
import operator
import arm_simd
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

intrin_re = re.compile(r'[a-z0-9_]+\s*([a-z0-9_]+)\s*\(.*')
def get_intrin_name(sig):
  return intrin_re.match(sig).group(1)

def select(vec, vec_ty, i):
  n = vec_ty.elem_size
  return z3.Extract(i * n + n - 1, i * n, vec)

def gen_non_simd(run, sig):
  vec_types = [parse_vector_type(arg.split()[0])
      for arg in sig[sig.index('(')+1:sig.index(')')].split(',')]
  elem_size, num_elems, is_signed, is_float = ty = parse_vector_type(sig.strip().split()[0])
  #evaluator = eval_ty(is_signed, is_float)
  vecs = [new_sym_val(elem_size * num_elems) for elem_size, num_elems, _, _ in vec_types]
  y = run(vecs, vec_types, ty)
  return vecs, z3.simplify(concat(list(reversed(y)))), ty, sig[:sig.index(')')+1]

def gen_simd(eval_ty, sig):
  def run(vecs, vec_types, ty):
    evaluator = eval_ty(ty.is_signed, ty.is_float)
    return [z3.Extract(ty.elem_size-1, 0, evaluator.run(x))
        for x in zip(*(split_vector(vec, vec_ty.elem_size)
          for vec, vec_ty in zip(vecs, vec_types)
    ))]
  return gen_non_simd(run, sig)

def gen_pairwise(binop_ty, sig):
  def run(vecs, vec_types, ty):
    evaluator = binop_ty(ty.is_signed, ty.is_float)
    y = []
    for x, x_ty in zip(vecs, vec_types):
      for i in range(x_ty.num_elems//2):
        y.append(z3.Extract(ty.elem_size-1, 0,
          evaluator.run(args=(select(x, x_ty, 2*i), select(x, x_ty, 2*i+1)))))
    return y
  return gen_non_simd(run, sig)

def gen_pairwise_accumulate(sig):
  def run(vecs, vec_types, ty):
    add = Evaluator(ty.is_signed, ty.is_float).add
    a, b = vecs
    a_ty, b_ty = vec_types
    assert a_ty == ty
    y = []
    for i in range(ty.num_elems):
      y.append(
          z3.Extract(ty.elem_size-1, 0,
          add(select(a, a_ty, i),
            add(select(b, b_ty, 2*i), select(b, b_ty, 2*i+1)))))
    return y
  return gen_non_simd(run, sig)

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

  def cmp_lt(self, a, b):
    if self.is_float:
      lt = fp_sema.binary_float_cmp('lt', use_uninterpreted=True)
      return lt(a, b)[0] == 1
    if not self.is_signed:
      return z3.ULT(a, b)
    return a < b

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

class AbsoluteDifference(Evaluator):
  def run(self, args):
    a, b = args
    return z3.If(self.cmp_lt(a, b), self.sub(b, a), self.sub(a, b))

class AbsoluteDifferenceAccumulate(Evaluator):
  def run(self, args):
    r, a, b = args
    return self.add(r, z3.If(self.cmp_lt(a, b), self.sub(b, a), self.sub(a, b)))

class Max(Evaluator):
  def run(self, args):
    a, b = args
    return z3.If(self.cmp_lt(a, b), b, a)

class Min(Evaluator):
  def run(self, args):
    a, b = args
    return z3.If(self.cmp_lt(a, b), a, b)

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
    'abd': AbsoluteDifference,
    'aba': AbsoluteDifferenceAccumulate,
    'max': Max,
    'min': Min,
    }

def gen_dot(sig):
  def run(vecs, vec_types, ty):
    r, a, b = vecs
    _, a_ty, b_ty = vec_types
    assert a_ty.num_elems == b_ty.num_elems
    n = a_ty.num_elems
    y = []
    for i in range(n // 4):
      s = select(r, ty, i)
      for j in range(4):
        aj = fix_bitwidth(select(a, a_ty, 4 * i + j), ty.elem_size, a_ty.is_signed)
        bj = fix_bitwidth(select(b, b_ty, 4 * i + j), ty.elem_size, b_ty.is_signed)
        s += aj * bj
      y.append(s)
    return y
  return gen_non_simd(run, sig)

def gen_matmul(sig):
  def run(vecs, vec_types, ty):
    r, a, b = vecs
    _, a_ty, b_ty = vec_types
    assert ty.elem_size == 32
    y = [None] * ty.num_elems
    for i in range(2):
      for j in range(2):
        s = select(r, ty, 2*i+j)
        for k in range(7):
          ak = fix_bitwidth(select(a, a_ty, 8 * i + k), ty.elem_size, a_ty.is_signed)
          bk = fix_bitwidth(select(b, b_ty, 8 * j + k), ty.elem_size, b_ty.is_signed)
          s += ak * bk
        y[2*i+j] = s
    return y
  return gen_non_simd(run, sig)

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
#print(gen_simd(AbsoluteDifference, 'int8x8_t    vabd_s8(int8x8_t a, int8x8_t b);         // VABD.S8 d0,d0,d0 '))
#print(gen_simd(AbsoluteDifference, 'float32x4_t vabdq_f32(float32x4_t a, float32x4_t b); // VABD.F32 q0,q0,q0'))
#print(gen_simd(AbsoluteDifference, 'uint64x2_t vabdl_u32(uint32x2_t a, uint32x2_t b);'))
#print(gen_simd(AbsoluteDifferenceAccumulate, 'int8x8_t   vaba_s8(int8x8_t a, int8x8_t b, int8x8_t c);'))
#print(gen_simd(AbsoluteDifferenceAccumulate, 'uint64x2_t vabal_u32(uint64x2_t a, uint32x2_t b, uint32x2_t c);'))
#print(gen_dot('uint32x2_t vdot_u32 (uint32x2_t r, uint8x8_t a, uint8x8_t b)'))
#print(gen_matmul('int32x4_t vusmmlaq_s32 (int32x4_t r, uint8x16_t a, int8x16_t b)'))
#print(gen_matmul('uint32x4_t vmmlaq_u32 (uint32x4_t r, uint8x16_t a, uint8x16_t b)'))
#exit()

padds = [
    "int8x8_t    vpadd_s8(int8x8_t a, int8x8_t b);        // VPADD.I8 d0,d0,d0 ",
    "int16x4_t   vpadd_s16(int16x4_t a, int16x4_t b);     // VPADD.I16 d0,d0,d0",
    "int32x2_t   vpadd_s32(int32x2_t a, int32x2_t b);     // VPADD.I32 d0,d0,d0",
    "uint8x8_t   vpadd_u8(uint8x8_t a, uint8x8_t b);      // VPADD.I8 d0,d0,d0 ",
    "uint16x4_t  vpadd_u16(uint16x4_t a, uint16x4_t b);   // VPADD.I16 d0,d0,d0",
    "uint32x2_t  vpadd_u32(uint32x2_t a, uint32x2_t b);   // VPADD.I32 d0,d0,d0",
    "float32x2_t vpadd_f32(float32x2_t a, float32x2_t b); // VPADD.F32 d0,d0,d0",
    "int16x4_t  vpaddl_s8(int8x8_t a);      // VPADDL.S8 d0,d0 ",
    "int32x2_t  vpaddl_s16(int16x4_t a);    // VPADDL.S16 d0,d0",
    "int64x1_t  vpaddl_s32(int32x2_t a);    // VPADDL.S32 d0,d0",
    "uint16x4_t vpaddl_u8(uint8x8_t a);     // VPADDL.U8 d0,d0 ",
    "uint32x2_t vpaddl_u16(uint16x4_t a);   // VPADDL.U16 d0,d0",
    "uint64x1_t vpaddl_u32(uint32x2_t a);   // VPADDL.U32 d0,d0",
    "int16x8_t  vpaddlq_s8(int8x16_t a);    // VPADDL.S8 q0,q0 ",
    "int32x4_t  vpaddlq_s16(int16x8_t a);   // VPADDL.S16 q0,q0",
    "int64x2_t  vpaddlq_s32(int32x4_t a);   // VPADDL.S32 q0,q0",
    "uint16x8_t vpaddlq_u8(uint8x16_t a);   // VPADDL.U8 q0,q0 ",
    "uint32x4_t vpaddlq_u16(uint16x8_t a);  // VPADDL.U16 q0,q0",
    "uint64x2_t vpaddlq_u32(uint32x4_t a);  // VPADDL.U32 q0,q0",
    ]

# long pairwise add and accumulate
adals = [
    "int16x4_t  vpadal_s8(int16x4_t a, int8x8_t b);      // VPADAL.S8 d0,d0 ",
    "int32x2_t  vpadal_s16(int32x2_t a, int16x4_t b);    // VPADAL.S16 d0,d0",
    "int64x1_t  vpadal_s32(int64x1_t a, int32x2_t b);    // VPADAL.S32 d0,d0",
    "uint16x4_t vpadal_u8(uint16x4_t a, uint8x8_t b);    // VPADAL.U8 d0,d0 ",
    "uint32x2_t vpadal_u16(uint32x2_t a, uint16x4_t b);  // VPADAL.U16 d0,d0",
    "uint64x1_t vpadal_u32(uint64x1_t a, uint32x2_t b);  // VPADAL.U32 d0,d0",
    "int16x8_t  vpadalq_s8(int16x8_t a, int8x16_t b);    // VPADAL.S8 q0,q0 ",
    "int32x4_t  vpadalq_s16(int32x4_t a, int16x8_t b);   // VPADAL.S16 q0,q0",
    "int64x2_t  vpadalq_s32(int64x2_t a, int32x4_t b);   // VPADAL.S32 q0,q0",
    "uint16x8_t vpadalq_u8(uint16x8_t a, uint8x16_t b);  // VPADAL.U8 q0,q0 ",
    "uint32x4_t vpadalq_u16(uint32x4_t a, uint16x8_t b); // VPADAL.U16 q0,q0",
    "uint64x2_t vpadalq_u32(uint64x2_t a, uint32x4_t b); // VPADAL.U32 q0,q0"
    ]

folding_maxs = [
    "int8x8_t    vpmax_s8(int8x8_t a, int8x8_t b);        // VPMAX.S8 d0,d0,d0 ",
    "int16x4_t   vpmax_s16(int16x4_t a, int16x4_t b);     // VPMAX.S16 d0,d0,d0",
    "int32x2_t   vpmax_s32(int32x2_t a, int32x2_t b);     // VPMAX.S32 d0,d0,d0",
    "uint8x8_t   vpmax_u8(uint8x8_t a, uint8x8_t b);      // VPMAX.U8 d0,d0,d0 ",
    "uint16x4_t  vpmax_u16(uint16x4_t a, uint16x4_t b);   // VPMAX.U16 d0,d0,d0",
    "uint32x2_t  vpmax_u32(uint32x2_t a, uint32x2_t b);   // VPMAX.U32 d0,d0,d0",
    "float32x2_t vpmax_f32(float32x2_t a, float32x2_t b); // VPMAX.F32 d0,d0,d0",
    ]

folding_mins = [
    "int8x8_t    vpmin_s8(int8x8_t a, int8x8_t b);        // VPMIN.S8 d0,d0,d0 ",
    "int16x4_t   vpmin_s16(int16x4_t a, int16x4_t b);     // VPMIN.S16 d0,d0,d0",
    "int32x2_t   vpmin_s32(int32x2_t a, int32x2_t b);     // VPMIN.S32 d0,d0,d0",
    "uint8x8_t   vpmin_u8(uint8x8_t a, uint8x8_t b);      // VPMIN.U8 d0,d0,d0 ",
    "uint16x4_t  vpmin_u16(uint16x4_t a, uint16x4_t b);   // VPMIN.U16 d0,d0,d0",
    "uint32x2_t  vpmin_u32(uint32x2_t a, uint32x2_t b);   // VPMIN.U32 d0,d0,d0",
    "float32x2_t vpmin_f32(float32x2_t a, float32x2_t b); // VPMIN.F32 d0,d0,d0",
    ]

dots = [
    "uint32x2_t vdot_u32 (uint32x2_t r, uint8x8_t a, uint8x8_t b)",
    "int32x2_t vdot_s32 (int32x2_t r, int8x8_t a, int8x8_t b)",
    "uint32x4_t vdotq_u32 (uint32x4_t r, uint8x16_t a, uint8x16_t b)",
    "int32x4_t vdotq_s32 (int32x4_t r, int8x16_t a, int8x16_t b)",
    #"int32x2_t vusdot_s32 (int32x2_t r, uint8x8_t a, int8x8_t b)",
    #"int32x4_t vusdotq_s32 (int32x4_t r, uint8x16_t a, int8x16_t b)",
    ]

matmuls = [
    #    "int32x4_t vmmlaq_s32 (int32x4_t r, int8x16_t a, int8x16_t b)",
    #    "uint32x4_t vmmlaq_u32 (uint32x4_t r, uint8x16_t a, uint8x16_t b)",
    #    "int32x4_t vusmmlaq_s32 (int32x4_t r, uint8x16_t a, int8x16_t b)",
    ]

semas = {}

for category, intrinsics in arm_simd.simds.items():
  evaluator_ty = evaluators[category]
  for intrin in intrinsics:
    semas[get_intrin_name(intrin)] = gen_simd(evaluator_ty, intrin)

for intrin in padds:
  semas[get_intrin_name(intrin)] = gen_pairwise(Add, intrin)

for intrin in adals:
  semas[get_intrin_name(intrin)] = gen_pairwise_accumulate(intrin)

for intrin in folding_maxs:
  semas[get_intrin_name(intrin)] = gen_pairwise(Max, intrin)

for intrin in folding_mins:
  semas[get_intrin_name(intrin)] = gen_pairwise(Min, intrin)

for intrin in dots:
  semas[get_intrin_name(intrin)] = gen_dot(intrin)

for intrin in matmuls:
  semas[get_intrin_name(intrin)] = gen_matmul(intrin)
