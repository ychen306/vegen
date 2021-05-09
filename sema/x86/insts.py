import sys
from pathlib import Path
sys.path.append(str(Path(__file__).parent.parent))
sys.path.append(str(Path(__file__).parent))

from intrinsic_types import intrinsic_types
from spec_serializer import load_spec
from manual_parser import parse_specs
import description as desc
import json

# default cost of intrinisc/instruction in case we don't know
DEFAULT_COST = 1

def parse_perf_file(fname, uarch='Skylake'):
  costs = {}
  with open(fname) as f:
    perf = json.load(f)
    for inst, data in perf.items():
      # data looks something like this [
      #      {"Broadwell":{l:"1",t:"1",}},
      #      {"Haswell":{l:"1",t:"1",}},
      #      {"Ivy Bridge":{l:"1",t:"1",}},
      #  ]
      for entry in data:
        if uarch not in entry:
          continue
        # throughput
        tp = entry[uarch]['t']
        if tp == '':
          continue
        costs[inst] = float(tp) / 0.5
  return costs

def get_element_size(spec):
  return int(spec.elem_type[2:])

def get_ctype_bitwidth(typename):
  if typename.endswith('*'):
    typename = typename[:-1].strip()
  return intrinsic_types[typename].bitwidth

def get_signature(spec):
  inputs = []
  for i, param in enumerate(spec.params):
    bitwidth = get_ctype_bitwidth(param.type)
    inputs.append(desc.Type(bitwidth=bitwidth, ctype=param.type, is_constant=param.is_imm, effective_width=spec.imm_width))

  assert spec.rettype != 'void'
  out_bitwidth = get_ctype_bitwidth(spec.rettype)
  output = desc.Type(bitwidth=out_bitwidth, ctype=spec.rettype)

  return desc.Signature(inputs, output)

costs = parse_perf_file(Path(__file__).parent / 'perf.json')
specs = parse_specs(Path(__file__).parent / 'data-latest.xml')

x86_insts = []
with open(Path(__file__).parent / 'intrinsics.all.sema') as sema_f:
  while True:
    line = next(sema_f, None)
    if line is None:
      break
    intrin = line.strip()

    xs, ys = load_spec(next(sema_f))

    # skip over instructions with multiple outputs
    if len(ys) != 1:
      continue
    [y] = ys

    spec = specs[intrin]
    # There are some instructions we don't (care to..) support
    try:
      sig = get_signature(spec)
      element_size = get_element_size(spec)
    except:
      pass
    inst = desc.Instruction(
        name=intrin,
        sig=sig,
        sema=desc.Semantics(inputs=xs, output=y),
        cost=costs.get(spec.xed, DEFAULT_COST),
        element_size=element_size,
        features=spec.cpuids
      )
    x86_insts.append(inst)
    if len(x86_insts) > 8:
      break
