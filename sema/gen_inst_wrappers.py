from semas import semas
from manual_parser import parse_specs
from sig import get_inst_sigs

def emit_wrapper(inst, input_types, spec, imm8, outf):
  assert spec.rettype != 'void'

  wrapper_name = f''
  params = ', '.join(
      f'{x.type} {x.name}' for x, x_ty in 
      zip(spec.params, input_types)
      if not x_ty.is_constant)
  args = ', '.join(
      x.name if not x_ty.is_constant else str(imm8)
      for x, x_ty in 
      zip(spec.params, input_types)
      )

  outf.write(f'''
{spec.rettype} intrinsic_wrapper_{inst}_{imm8}({params}) {{
  return {inst}({args});
}}''')


specs = parse_specs('data-latest.xml')
sigs = get_inst_sigs(semas, specs)

with open('InstWrappers.c', 'w') as outf:
  outf.write('''
#include <immintrin.h>
#define __int64_t __int64
#define __int64 long long''')

  for inst, (xs, ys) in sigs.items():
    if len(ys) != 1:
      continue

    [y] = ys
    spec = specs[inst]
    has_imm = any(x.is_constant for x in xs)

    if not has_imm:
      emit_wrapper(inst, xs, spec, 0, outf)
    else:
      for imm in range(1<<specs[inst].imm_width):
        emit_wrapper(inst, xs, spec, imm, outf)

with open('inst_wrappers.flags', 'w') as outf:
  cpuids = set()
  for inst in semas.keys():
    for cpuid in specs[inst].cpuids:
      cpuids.add(cpuid)
  outf.write(' '.join('-m'+cpuid for cpuid in cpuids))
