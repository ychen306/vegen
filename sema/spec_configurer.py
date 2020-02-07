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
<intrinsic tech='SSSE3' vexEq='TRUE' rettype='__m128i' name='_mm_mulhrs_epi16'>
	<type>Integer</type>
	<CPUID>SSSE3</CPUID>
	<category>Arithmetic</category>
	<parameter varname='a' type='__m128i'/>
	<parameter varname='b' type='__m128i'/>
	<description>Multiply packed 16-bit integers in "a" and "b", producing intermediate signed 32-bit integers. Truncate each intermediate integer to the 18 most significant bits, round by adding 1, and store bits [16:1] to "dst". </description>
	<operation>
FOR j := 0 to 7
	i := j*16
	tmp[31:0] := ((a[i+15:i] * b[i+15:i]) &gt;&gt; 14) + 1
	dst[i+15:i] := tmp[16:1]
ENDFOR
	</operation>
	<instruction name='pmulhrsw' form='xmm, xmm'/>
	<header>tmmintrin.h</header>
</intrinsic>
  '''

  intrin_node = ET.fromstring(sema)
  spec = get_spec_from_xml(intrin_node)
  ok, compiled, new_spec = configure_spec(spec, num_tests=100)
  print(ok, compiled)
