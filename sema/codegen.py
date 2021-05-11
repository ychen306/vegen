import gen_rules
import description as desc
from typing import List
from lift_sema import Translator, reduce_bitwidth, elim_dead_branches, elim_redundant_branches
import gen_rules
from tqdm import tqdm

def preprocess(y):
  return reduce_bitwidth(elim_redundant_branches(elim_dead_branches(y)))

def emit_instruction_bindings(insts : List[desc.Instruction], binding_vector_name, outf):
  bundles = {}

  pbar = tqdm(insts)
  for inst in pbar:
    translator = Translator()
    pbar.set_description('processing '+inst.name)
    try:
      out_ids, dag = translator.translate_formula(preprocess(inst.sema.output), inst.element_size)
    except:
      print('failed to lift', inst.name)
      continue

    try:
      rb = gen_rules.RuleBundle(inst.sig, inst.sema, out_ids, dag)
    except:
      print('failed to generate pattern matching rule for', inst.name)
      continue

    # TODO: remove these restrictions
    if not rb.all_lanes_simple():
      print(inst.name, 'yucky lanes')
      continue
    if rb.has_nop():
      print(inst.name, 'has noop lane')
      continue

    bundles[inst.name] = rb
  
  features = {inst.name: inst.features for inst in insts}
  costs = {inst.name: inst.cost for inst in insts}

  outf.write('''#include "InstSema.h"
#include "MatchingUtil.h"

using namespace llvm;
using namespace PatternMatch;
    ''')

  outf.write(gen_rules.codegen(bundles, features, costs, binding_vector_name=binding_vector_name))

def emit_wrapper(inst, imm8, outf):
  params = ', '.join(
      f'{x.ctype} tmp{i} ' for i, x in enumerate(inst.sig.inputs)
      if not x.is_constant)
  args = ', '.join(
      f'tmp{i}' if not x.is_constant else str(imm8)
      for i, x in enumerate(inst.sig.inputs))
  outf.write(f'''
{inst.sig.output.ctype} intrinsic_wrapper_{inst.name}_{imm8}({params}) {{
  return {inst.name}({args});
}}''')

def emit_wrappers(insts: List[desc.Instruction], outf):
  for inst in insts:
    has_imm = any(x.is_constant for x in inst.sig.inputs)
    if not has_imm:
      emit_wrapper(inst, 0, outf)
    else:
      imm_width = next(x.effective_width for x in inst.sig.inputs if x.is_constant)
      # FIXME: what if the immediate width is larger
      for imm in range(1<<imm_width):
        emit_wrapper(inst, imm, outf)
