from fp_sema import set_precision

set_precision(False)

from spec_serializer import load_spec
import itertools
import z3

# mapping <intrinsic name> -> [<in vars>], [<out formulas>]
semas = {}

# get semantics of intrinsics
#with open('intrinsics.avx2.sema') as sema_f:
with open('intrinsics.avx512.sema') as sema_f:
  while True:
    intrin_name = next(sema_f, None)
    if intrin_name is None:
      break

    spec = next(sema_f)
    #if 'fp' in spec:
    #  continue

    #if 'mask' not in intrin_name:
    #  continue
    #if 'add_epi32' not in intrin_name:
    #  continue
    #if intrin_name.strip() == '_ktest_mask8_u8':
    #  f = load_spec(spec)[1][0]
    #  z3.simplify(f)
    #  print(f)
    #  print('=============')
    #  print(f.sexpr())
    #  exit(1)

    sema = load_spec(spec)
    semas[intrin_name.strip()] = sema
    _, ys = sema

# return a map <ret type> -> [ insts ]
def categorize_insts(semas):
  categories = defaultdict(list)
  for inst, (_, outs) in semas.items():
    out_sig = tuple(out.size() for out in outs)
    categories[out_sig].append(inst)
  return categories
