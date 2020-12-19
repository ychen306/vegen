from arm_semas import semas, type_re
import sys

with open('InstWrappers.arm.c', 'w') as f:
  f.write('#include <arm_neon.h>\n')
  for intrin, (_, _, _, decl) in semas.items():
    f.write(decl.replace(intrin, 'intrinsic_wrapper_'+intrin+'_0') + ' {\n')
    f.write('  return %s;\n' % type_re.sub('', decl))
    f.write('}\n')
