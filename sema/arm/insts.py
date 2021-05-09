import description as desc
from . import arm_semas

def get_arg_types(decl):
  return [
      arg.strip().split(' ')[0]
      for arg in decl[decl.index('(')+1:decl.index(')')].split(',')]

def get_output_type(decl):
  return decl.split(' ')[0]

def create_description(intrin, sema):
  xs, y, out_ty, decl = sema
  ctypes = get_arg_types(decl)
  input_types = [desc.Type(x.size(), ctype) for x, ctype in zip(xs, ctypes)]
  output_type = desc.Type(y.size(), get_output_type(decl))
  sig = desc.Signature(input_types, output_type)
  return desc.Instruction(
      name=intrin,
      sig=sig,
      sema=desc.Semantics(xs, y),
      cost=1, # TODO
      element_size=out_ty.elem_size,
      features=[] # TODO
      )

arm_insts = [create_description(intrin, sema) for intrin, sema in arm_semas.semas.items()]
