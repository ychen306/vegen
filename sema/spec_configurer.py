'''
Many operators are ambiguously defined in the manual.
For instance, '<' is used to compare both signed and unsigned bitvectors.
'''
from fuzzer import fuzz_intrinsic
from compiler import set_bitwidth_minimization
import itertools

# these operators are ambiguously defined (so far as signedness is concerned)
configurable_op = {
    '<', '<=',
    '>', '>=',
    '>>',
    '*', '+', '-',
    }

def configure_spec(spec, num_tests=10, num_iters=32):
  '''
  given a spec, configure its binary operators so that
  the spec conforms with real-world behavior.

  return <success?>, <spec>
  '''
  ok, compiled = fuzz_intrinsic(spec, num_tests)
  if not compiled:
    # we don't have the groundtruth
    #  if we can't even compile code using this intrinsic
    return False, False, spec

  if ok: # already correct spec
    # now turn on bitwidth minimization and see if it's still correct
    set_bitwidth_minimization(True)
    ok, _ = fuzz_intrinsic(spec, num_tests)
    set_bitwidth_minimization(False)
    return ok, True, spec

  configurable_exprs = [expr 
      for expr in spec.binary_exprs if expr.op in configurable_op]

  postfix = spec.intrin.split('_')[-1]
  epi = postfix.startswith('epi')
  epu = postfix.startswith('epu')
  if epi or epu:
    # try to make everything unsigned or signed
    configs = {
        expr.expr_id: epi
        for expr in configurable_exprs
        }
    new_spec = spec._replace(configs=configs)
    ok, _ = fuzz_intrinsic(new_spec)
    if ok:
      # now turn on bitwidth minimization and see if it's still correct
      set_bitwidth_minimization(True)
      ok, _ = fuzz_intrinsic(new_spec, num_tests)
      set_bitwidth_minimization(False)
      return ok, True, new_spec

  num_configs = len(configurable_exprs)
  config_space = itertools.product(*[(True, False) for _ in range(num_configs)])
  for i, encoded_config in enumerate(config_space):
    if i >= num_iters:
      break
    configs = {
        expr.expr_id: signedness 
        for expr, signedness in zip(configurable_exprs, encoded_config)
        }
    new_spec = spec._replace(configs=configs)
    ok, _ = fuzz_intrinsic(new_spec)
    if ok:
      # now turn on bitwidth minimization and see if it's still correct
      set_bitwidth_minimization(True)
      ok, _ = fuzz_intrinsic(new_spec, num_tests)
      set_bitwidth_minimization(False)
      return ok, True, new_spec
  return False, True, spec

if __name__ == '__main__':
  import sys
  import xml.etree.ElementTree as ET
  from manual_parser import get_spec_from_xml

  sema = '''
<intrinsic tech='AVX-512' rettype='__m512i' name='_mm512_maskz_dpwssd_epi32'>
	<type>Integer</type>
	<CPUID>AVX512_VNNI</CPUID>
	<category>Arithmetic</category>
	<parameter varname='k' type='__mmask16'/>
	<parameter varname='src' type='__m512i'/>
	<parameter varname='a' type='__m512i'/>
	<parameter varname='b' type='__m512i'/>
	<description>
		Multiply groups of 2 adjacent pairs of signed 16-bit integers in "a" with corresponding 16-bit integers in "b", producing 2 intermediate signed 32-bit results. Sum these 2 results with the corresponding 32-bit integer in "src", and store the packed 32-bit results in "dst" using zeromask "k" (elements are zeroed out when the corresponding mask bit is not set).
	</description>
	<operation>
FOR j := 0 to 15
	IF k[j]
		tmp1 := a.word[2*j] * b.word[j]
		tmp2 := a.word[2*j+1] * b.word[j+1]
		dst.dword[j] := src.dword[j] + tmp1 + tmp2
	ELSE
		dst.dword[j] := 0
	FI
ENDFOR
dst[MAX:512] := 0
	</operation>
	<instruction name='VPDPWSSD' form='zmm {k}, zmm, zmm' xed=''/>
	<header>immintrin.h</header>
</intrinsic>
  '''

  intrin_node = ET.fromstring(sema)
  spec = get_spec_from_xml(intrin_node)
  ok, compiled, new_spec = configure_spec(spec, num_tests=5)
  print(ok, compiled)
