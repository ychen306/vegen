import codegen
from x86.insts import x86_insts

with open('InstSema.x86.cpp', 'w') as f:
  codegen.emit_instruction_bindings(x86_insts[:4], 'X86Insts', f)

with open('InstWrappers.x86.c', 'w') as f:
  f.write('''#include <immintrin.h>
#define __int64_t __int64
#define __int64 long long''')
  codegen.emit_wrappers(x86_insts, f)
