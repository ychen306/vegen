from intrinsic_types import intrinsic_types, is_float
from bitstring import Bits, BitArray
import random
from tempfile import NamedTemporaryFile
import os
import subprocess
from compiler import compile
from bit_util import *
import math
import z3
import functools
import operator
from spec_serializer import dump_spec, load_spec
from z3_utils import get_used_bit_range

src_path = os.path.dirname(os.path.abspath(__file__))

def get_imm_mask(imm8, outs):
  '''
  Given imm8 and the semantic of the outputs,
  figure out a mask that identifies the bits of imm8
  that are actually useful
  '''
  br = get_used_bit_range(outs[0], imm8)
  if br is None:
    return None
  lo, hi = br
  # hi is exclusive
  return (1 << hi) - 1

def extract_float(bv, i, bitwidth):
  '''
  extract i'th float from bv

  bitwidth is the size of a one floating point (either 32 or 64)
  '''
  if bitwidth == 32:
    ty = z3.Float32()
  else:
    assert bitwidth == 64
    ty = z3.Float64()
  sub_bv = z3.Extract(i * bitwidth + bitwidth - 1, i * bitwidth, bv)
  return z3.fpBVToFP(sub_bv, ty)

def equal(a, b, ty):
  if is_float(ty):
    if ty.is_float:
      elem_bw = 32
    else:
      elem_bw = 64
    assert ty.bitwidth % elem_bw == 0
    num_elems = ty.bitwidth // elem_bw
    return z3.Or(a == b, z3.And([
        z3.fpAbs(extract_float(a, i, elem_bw) - extract_float(b, i, elem_bw)) < 1e-5
        for i in range(num_elems)]))
  return a == b

def check_compiled_spec_with_examples(param_vals, outs, out_types, inputs, expected_outs):
  s = z3.Solver()
  s.set(timeout=20000)
  constraints = []
  for input, expected in zip(inputs, expected_outs):
    subs = [(param, z3.BitVecVal(x, param.size())) for param, x in zip(param_vals, input)]
    outs_concrete = [z3.simplify(z3.substitute(out, *subs))
        for out in outs]
    ############
    #y_hat = outs_concrete[0].as_long()
    #y = expected[0]
    #print('Wrong:', bin(y_hat ^ y))
    ############

    constraints.append(
        z3.And([equal(z3.BitVecVal(y_expected, y.size()), y, out_type)
          for y_expected, y, out_type in zip(expected, outs_concrete, out_types)]))
  spec_correct = z3.And(constraints)
  s.add(z3.Not(spec_correct))
  correct = s.check() == z3.unsat
  #if not correct:
  #  print(s.model().evaluate(outs[0]), expected_outs[0][0])
  return correct


def line_to_bitvec(line, ty):
  qwords = list(map(int, line.split()))
  if ty.bitwidth <= 64:
    assert len(qwords) == 1
    [bits] = qwords
    mask = (1 << ty.bitwidth) - 1
    return bits & mask

  assert ty.bitwidth % 64 == 0
  components = [bits << (i * 64) for i, bits in enumerate(qwords)]
  return functools.reduce(operator.or_, components, 0)


load_intrinsics = {
    '_m512i': '_mm512_loadu_si512',
    '__m512i': '_mm512_loadu_si512',
    '__m256i': '_mm256_loadu_si256',
    '__m128i': '_mm_loadu_si128',

    # single precision floats
    '__m512': '_mm512_loadu_ps',
    '__m256': '_mm256_loadu_ps',
    '__m128': '_mm_loadu_ps',
    '_m512': '_mm512_loadu_ps',
    '_m256': '_mm256_loadu_ps',
    '_m128': '_mm_loadu_ps',

    # double precision floats
    '__m512d': '_mm512_loadu_pd',
    '__m256d': '_mm256_loadu_pd',
    '__m128d': '_mm_loadu_pd',
    '_m512d': '_mm512_loadu_pd',
    '_m256d': '_mm256_loadu_pd',
    '_m128d': '_mm_loadu_pd',
    }

# functions that prints these vector registers
printers = {
    '_m512i': 'print__m512i',
    '__m512i': 'print__m512i',
    '__m256i': 'print__m256i',
    '__m128i': 'print__m128i',

    # single precision floats
    '__m512': 'print__m512i',
    '__m256': 'print__m256i',
    '__m128': 'print__m128i',
    '_m512': 'print__m512i',
    '_m256': 'print__m256i',
    '_m128': 'print__m128i',

    # double precision floats
    '__m512d': 'print__m512i',
    '__m256d': 'print__m256i',
    '__m128d': 'print__m128i',
    '_m512d': 'print__m512i',
    '_m256d': 'print__m256i',
    '_m128d': 'print__m128i',
    }

def emit_load(outf, dst, src, typename):
  if typename in load_intrinsics:
    load_intrinsic = load_intrinsics[typename]
    outf.write('%s %s = %s((%s *)%s);\n' % (
      typename, dst, load_intrinsic, typename, src
      ))
  else:
    outf.write('%s %s = *(%s *)(%s);\n' % (
      typename, dst, typename, src
      ))

def gen_rand_data(outf, name, typename):
  '''
  declare a variable of `data_type` called `name`

  print result to `outf` and return the actual bytes in bits

  e.g. for ty=__m512i, name = x1, we declare the following

  unsigned char x1[64] = { ... };
  '''

  if typename.endswith('*'):
    is_pointer = True
    typename = typename[:-1].strip()
  else:
    is_pointer = False

  ty = intrinsic_types[typename]

  # generate floats separates for integer because we don't
  #  want to deal with underflow and other floating point issues
  if not is_float(ty):
    num_bytes = ty.bitwidth // 8
    bytes = [random.randint(0, 255) for _ in range(num_bytes)]
    outf.write('unsigned char %s_aux[%d] = { %s };\n' % (
      name, num_bytes, ','.join(map(str, bytes))
      ))
    bits = BitArray(length=ty.bitwidth)
    for i, byte in enumerate(bytes):
      update_bits(bits, i*8, i*8+8, byte)
  else:
    float_size = 32 if ty.is_float else 64
    c_type = 'float' if ty.is_float else 'double'
    num_floats = ty.bitwidth // float_size
    floats = [random.random() for _ in range(num_floats)]
    outf.write('%s %s_aux[%d] = { %s };\n' % (
      c_type, name, num_floats, ','.join(map(str, floats))
      ))
    bits = float_vec_to_bits(floats, float_size=float_size)

  if not is_pointer:
    # in this case we need to load the bytes
    emit_load(outf, src='%s_aux'%name, dst=name, typename=typename)
  else:
    # in this case we just take the address
    outf.write('%s *%s = (%s *)(&%s_aux);\n' % (
        typename, name, typename, name 
      ))

  return bits

def emit_print(outf, var, typename):
  if typename.endswith('*'):
    typename = typename[:-1].strip()
    ty = intrinsic_types[typename]
    is_pointer = True
  else:
    is_pointer = False
    ty = intrinsic_types[typename]

  if is_pointer:
    # need to load the value first first
    tmp = get_temp_name()
    emit_load(outf, dst=tmp, src=var, typename=typename)
    var = tmp

  if typename in printers:
    # use the predefined printers
    printer = printers[typename]
    if ty.is_float:
      param_ty = 'unsigned long'
    elif ty.is_double:
      param_ty = 'unsigned long'
    else:
      param_ty = 'unsigned long'

    outf.write('%s((%s *)&%s);\n' % (printer, param_ty, var))
  else:
    if ty.is_float:
      outf.write('printf("%%u\\n", float2int(%s));\n' % var)
    elif ty.is_double:
      outf.write('printf("%%lu\\n", double2long(%s));\n' % var)
    else:
      outf.write('printf("%%lu\\n", (unsigned long)%s);\n' % var)


counter = 0
def get_temp_name():
  global counter
  counter += 1
  return 'tmp%d' % counter

def fuzz_intrinsic_once(outf, spec, sema):
  '''
  1) generate test (in C) that exercises the intrinsic
  2) run the interpreter per the spec and return the expected output
  '''
  xs, ys = sema

  # generate random arguments
  c_vars = []
  arg_vals = []
  out_params = []
  out_param_types = []
  inst_form = spec.inst_form.split(', ')
  no_imm8 = 'imm8' not in (param.name for param in spec.params)
  # TODO: refactor out this signature parsing logic
  for i, param in enumerate(spec.params):
    if ((no_imm8 and i < len(inst_form) and inst_form[i] == 'imm') or
        param.name == 'imm8'):
      param_id = len(arg_vals)
      mask = get_imm_mask(xs[param_id], ys)
      if mask is not None:
        byte = random.randint(0, 255) & mask
      else:
        # no bits used in this imm8... just set it to 0
        byte = 0
      c_vars.append(str(byte))
      arg_vals.append(Bits(uint=byte, length=8))
      continue
    c_var = get_temp_name()
    arg_val = gen_rand_data(outf, c_var, param.type)
    c_vars.append(c_var)
    arg_vals.append(arg_val)
    if param.type.endswith('*'):
      out_params.append(c_var)
      out_param_types.append(param.type[:-1].strip())

  # call the intrinsic
  has_return_val = spec.rettype != 'void'
  if has_return_val:
    ret_var = get_temp_name()
    outf.write('%s %s = %s(%s);\n' % (
      spec.rettype, ret_var, spec.intrin, ','.join(c_vars)
      ))
    # print the result
    emit_print(outf, ret_var, spec.rettype)
  else:
    outf.write('%s(%s);\n' % (
      spec.intrin, ','.join(c_vars)
      ))

  out_types = []

  for param, param_type in zip(out_params, out_param_types):
    emit_print(outf, param, param_type+'*')

  return arg_vals, out_param_types, has_return_val

def get_err(a, b, is_float):
  err = a - b
  if not is_float:
    return err
  if math.isnan(a) and math.isnan(b):
    return 0
  return err

def identical_vecs(a, b, is_float):
  errs = [get_err(aa, bb, is_float)
      for aa,bb in zip(a, b)]
  if is_float:
    return all(abs(err) <= 1e-6 for err in errs)
  return all(err == 0 for err in errs)

def bits_to_vec(bits, typename):
  if typename.endswith('*'):
    ty = intrinsic_types[typename[:-1]]
  else:
    ty = intrinsic_types[typename]
  if ty.is_float:
    return bits_to_float_vec(bits, float_size=32)
  elif ty.is_double:
    return bits_to_float_vec(bits, float_size=64)

  # integer type
  return bits_to_long_vec(bits)

def fuzz_intrinsic(spec, num_tests=100):
  '''
  spec -> (spec correct, can compile)
  '''
  param_vals, outs = compile(spec)
  sema = param_vals, outs
  interpreted = []
  exe = NamedTemporaryFile(delete=False)
  exe.close()
  with NamedTemporaryFile(suffix='.c', mode='w') as outf:
    outf.write('''
#include <emmintrin.h> 
#include <immintrin.h>
#include <nmmintrin.h>
#include <pmmintrin.h>
#include <smmintrin.h>
#include <tmmintrin.h>
#include <wmmintrin.h>
#include <xmmintrin.h>

#include <stdio.h>
#include "printers.h"

#define __int64_t __int64
#define __int64 long long

union float_and_int {
  float f;
  unsigned int i;
};

union double_and_long {
  double d;
  unsigned long l;
};

unsigned int float2int(float f) {
  union float_and_int x;
  x.f = f;
  return x.i;
}

unsigned long double2long(double d) {
  union double_and_long x;
  x.d = d;
  return x.l;
}

int main() {
        ''')

    x = []
    y = []
    for _ in range(num_tests):
      arg_vals, out_param_types, has_return_val = fuzz_intrinsic_once(outf, spec, sema)
      out_types = [intrinsic_types[ty] for ty in out_param_types]
      if spec.rettype != 'void':
        out_types = [intrinsic_types[spec.rettype]] + out_types
      x.append([val.uint for val in arg_vals])

    outf.write('''
  return 0;
}
      ''')
    outf.flush()

    os.system('cp %s %s' % (outf.name, 'debug.c'))

    features = ' '.join('-m'+cpuid for cpuid in spec.cpuids)

    # TODO: add CPUIDs 
    try:
      subprocess.check_output(
          'clang %s -o %s -I%s %s/printers.o %s 2>/dev/null >/dev/null' % (
            outf.name, exe.name, src_path, src_path, features),
          shell=True)
    except subprocess.CalledProcessError:
      return False, False

    num_outputs_per_intrinsic = len(out_types)

    stdout = subprocess.check_output(['sde64', '--', exe.name])
    lines = stdout.decode('utf-8').strip().split('\n')
    assert(len(lines) == num_tests * num_outputs_per_intrinsic)

  os.system('rm '+exe.name)

  for i in range(0, len(lines), num_outputs_per_intrinsic):
    outputs = []
    for ty, line in zip(out_types, lines[i:i+num_outputs_per_intrinsic]):
      outputs.append(line_to_bitvec(line, ty))
    y.append(outputs)

  correct = check_compiled_spec_with_examples(param_vals, outs, out_types, x, y)
  return correct, True

if __name__ == '__main__':
  import sys
  import xml.etree.ElementTree as ET
  from manual_parser import get_spec_from_xml
  from intrinsic_types import IntegerType

  sema = '''
<intrinsic tech="AVX" name="_mm256_dp_ps">
	<type>Floating Point</type>
	<CPUID>AVX</CPUID>
	<category>Arithmetic</category>
	<return type="__m256" varname="dst" etype="FP32"/>
	<parameter type="__m256" varname="a" etype="FP32"/>
	<parameter type="__m256" varname="b" etype="FP32"/>
	<parameter type="const int" varname="imm8" etype="IMM" immwidth="8"/>
	<description>Conditionally multiply the packed single-precision (32-bit) floating-point elements in "a" and "b" using the high 4 bits in "imm8", sum the four products, and conditionally store the sum in "dst" using the low 4 bits of "imm8".</description>
	<operation>
DEFINE DP(a[127:0], b[127:0], imm8[7:0]) {
	FOR j := 0 to 3
		i := j*32
		IF imm8[(4+j)%8]
			temp[i+31:i] := a[i+31:i] * b[i+31:i]
		ELSE
			temp[i+31:i] := FP32(0.0)
		FI
	ENDFOR
	
	sum[31:0] := (temp[127:96] + temp[95:64]) + (temp[63:32] + temp[31:0])
	
	FOR j := 0 to 3
		i := j*32
		IF imm8[j%8]
			tmpdst[i+31:i] := sum[31:0]
		ELSE
			tmpdst[i+31:i] := FP32(0.0)
		FI
	ENDFOR
	RETURN tmpdst[127:0]
}
dst[127:0] := DP(a[127:0], b[127:0], imm8[7:0])
dst[255:128] := DP(a[255:128], b[255:128], imm8[7:0])
dst[MAX:256] := 0
	</operation>
	<instruction name="VDPPS" form="ymm, ymm, ymm, imm8" xed="VDPPS_YMMqq_YMMqq_YMMqq_IMMb"/>
	<header>immintrin.h</header>
</intrinsic>
'''
  sema = '''
<intrinsic tech="SSSE3" vexEq="TRUE" name="_mm_maddubs_epi16">
	<type>Integer</type>
	<CPUID>SSSE3</CPUID>
	<category>Arithmetic</category>
	<return type="__m128i" varname="dst" etype="SI16"/>
	<parameter type="__m128i" varname="a" etype="UI8"/>
	<parameter type="__m128i" varname="b" etype="SI8"/>
	<description>Vertically multiply each unsigned 8-bit integer from "a" with the corresponding signed 8-bit integer from "b", producing intermediate signed 16-bit integers. Horizontally add adjacent pairs of intermediate signed 16-bit integers, and pack the saturated results in "dst".</description>
	<operation>
FOR j := 0 to 7
	i := j*16
	dst[i+15:i] := Saturate16( a[i+15:i+8]*b[i+15:i+8] + a[i+7:i]*b[i+7:i] )
ENDFOR
dst[MAX:256] := 0
	</operation>
	<instruction name="PMADDUBSW" form="xmm, xmm" xed="PMADDUBSW_XMMdq_XMMdq"/>
	<header>tmmintrin.h</header>
</intrinsic>
  '''
  sema = '''
<intrinsic tech="AVX2" name="_mm256_shuffle_epi8">
	<type>Integer</type>
	<CPUID>AVX2</CPUID>
	<category>Swizzle</category>
	<return type="__m256i" varname="dst" etype="UI8"/>
	<parameter type="__m256i" varname="a" etype="UI8"/>
	<parameter type="__m256i" varname="b" etype="UI8"/>
	<description>Shuffle 8-bit integers in "a" within 128-bit lanes according to shuffle control mask in the corresponding 8-bit element of "b", and store the results in "dst".</description>
	<operation>
FOR j := 0 to 15
	i := j*8
	IF b[i+7] == 1
		dst[i+7:i] := 0
	ELSE
		index[3:0] := b[i+3:i]
		dst[i+7:i] := a[index*8+7:index*8]
	FI
	IF b[128+i+7] == 1
		dst[128+i+7:128+i] := 0
	ELSE
		index[3:0] := b[128+i+3:128+i]
		dst[128+i+7:128+i] := a[128+index*8+7:128+index*8]
	FI
ENDFOR
dst[MAX:256] := 0
	</operation>
	<instruction name="VPSHUFB" form="ymm, ymm, ymm" xed="VPSHUFB_YMMqq_YMMqq_YMMqq"/>
	<header>immintrin.h</header>
</intrinsic>
  '''
  sema = '''
<intrinsic tech="AVX-512" name="_mm256_mask_max_epi8">
	<type>Integer</type>
	<CPUID>AVX512VL</CPUID>
	<CPUID>AVX512BW</CPUID>
	<category>Arithmetic</category>
	<return type="__m256i" varname="dst" etype="UI8"/>
	<parameter type="__m256i" varname="src" etype="UI8"/>
	<parameter type="__mmask32" varname="k" etype="MASK"/>
	<parameter type="__m256i" varname="a" etype="SI8"/>
	<parameter type="__m256i" varname="b" etype="SI8"/>
	<description>Compare packed signed 8-bit integers in "a" and "b", and store packed maximum values in "dst" using writemask "k" (elements are copied from "src" when the corresponding mask bit is not set).</description>
	<operation>
FOR j := 0 to 31
	i := j*8
	IF k[j]
		dst[i+7:i] := MAX(a[i+7:i], b[i+7:i])
	ELSE
		dst[i+7:i] := src[i+7:i]
	FI
ENDFOR
dst[MAX:256] := 0
	</operation>
	<instruction name="VPMAXSB" form="ymm {k}, ymm, ymm" xed="VPMAXSB_YMMi8_MASKmskw_YMMi8_YMMi8_AVX512"/>
	<header>immintrin.h</header>
</intrinsic>
  '''
  sema = '''
<intrinsic tech="AVX2" name="_mm256_min_epu16">
	<type>Integer</type>
	<CPUID>AVX2</CPUID>
	<category>Special Math Functions</category>
	<return type="__m256i" varname="dst" etype="UI16"/>
	<parameter type="__m256i" varname="a" etype="UI16"/>
	<parameter type="__m256i" varname="b" etype="UI16"/>
	<description>Compare packed unsigned 16-bit integers in "a" and "b", and store packed minimum values in "dst".</description>
	<operation>
FOR j := 0 to 15
	i := j*16
	dst[i+15:i] := MIN(a[i+15:i], b[i+15:i])
ENDFOR
dst[MAX:256] := 0
	</operation>
	<instruction name="VPMINUW" form="ymm, ymm, ymm" xed="VPMINUW_YMMqq_YMMqq_YMMqq"/>
	<header>immintrin.h</header>
</intrinsic>
'''
  sema = '''
<intrinsic tech="AVX2" name="_mm256_max_epu8">
	<type>Integer</type>
	<CPUID>AVX2</CPUID>
	<category>Special Math Functions</category>
	<return type="__m256i" varname="dst" etype="UI8"/>
	<parameter type="__m256i" varname="a" etype="UI8"/>
	<parameter type="__m256i" varname="b" etype="UI8"/>
	<description>Compare packed unsigned 8-bit integers in "a" and "b", and store packed maximum values in "dst".</description>
	<operation>
FOR j := 0 to 31
	i := j*8
	dst[i+7:i] := MAX(a[i+7:i], b[i+7:i])
ENDFOR
dst[MAX:256] := 0
	</operation>
	<instruction name="VPMAXUB" form="ymm, ymm, ymm" xed="VPMAXUB_YMMqq_YMMqq_YMMqq"/>
	<header>immintrin.h</header>
</intrinsic>
'''
  intrin_node = ET.fromstring(sema)
  spec = get_spec_from_xml(intrin_node)
  ok = fuzz_intrinsic(spec, num_tests=100)
  print(ok)
