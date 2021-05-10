import codegen
from arm.insts import arm_insts

with open('InstSema.arm.cpp', 'w') as f:
  codegen.emit_instruction_bindings(arm_insts, 'ArmInsts', f)

with open('InstWrappers.arm.c', 'w') as f:
  f.write('#include <arm_neon.h>\n')
  codegen.emit_wrappers(arm_insts, f)
