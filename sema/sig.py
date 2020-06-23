from intrinsic_types import intrinsic_types
from collections import namedtuple

InputType = namedtuple('InputType', ['bitwidth', 'is_constant'])

def get_ctype_bitwidth(typename):
  if typename.endswith('*'):
    typename = typename[:-1].strip()
  return intrinsic_types[typename].bitwidth

def get_intrinsic_signature(spec):
  '''
  given spec, return ([<input type>], [<output size>])
  '''
  input_types = []
  output_sizes = []
  inst_form = spec.inst_form.split(', ')
  no_imm8 = 'imm8' not in (param.name for param in spec.params)
  for i, param in enumerate(spec.params):
    bitwidth = get_ctype_bitwidth(param.type)

    if ((no_imm8 and i < len(inst_form) and inst_form[i] == 'imm') or
        param.name == 'imm8'):
      input_types.append(InputType(bitwidth=bitwidth, is_constant=True))
      continue

    if param.type.endswith('*'):
      output_sizes.append(bitwidth)
    else:
      input_types.append(InputType(bitwidth=bitwidth, is_constant=False))
  if spec.rettype != 'void':
    out_bitwidth = get_ctype_bitwidth(spec.rettype)
    output_sizes = [out_bitwidth,] + output_sizes
  return tuple(input_types), tuple(output_sizes)

def get_inst_sigs(semas, specs):
  sigs = {}
  for inst, (in_vals, out_vals) in semas.items():
    if inst in specs:
      sigs[inst] = get_intrinsic_signature(specs[inst])
    else:
      input_types = tuple(InputType(x.size(), is_constant=False) for x in in_vals)
      output_sizes = tuple(y.size() for y in out_vals)
      sigs[inst] = input_types, output_sizes
  return sigs


