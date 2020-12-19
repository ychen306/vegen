from lift_sema import Translator, reduce_bitwidth, typecheck
from arm_semas import semas
import functools
import sys
from tqdm import tqdm
import pickle

outf = sys.argv[1]

lifted = {}

debug = 'vpaddl_u32'
debug = None
if debug is not None:
  translator = Translator()
  xs, y, y_ty = semas[debug]
  liveins = [x.decl().name() for x in xs]
  y_reduced = reduce_bitwidth(y)
  y = y_reduced
  translator.translate_formula(y, y_ty.elem_size)
  exit()

pbar = tqdm(iter(semas.items()), total=len(semas))
for inst, sema in pbar:
  translator = Translator()
  xs, y, y_ty = sema
  liveins = [x.decl().name() for x in xs]
  y_reduced = reduce_bitwidth(y)
  y = y_reduced

  try:
    outs, dag = translator.translate_formula(y, y_ty.elem_size)
    assert typecheck(dag)
    lifted[inst] = liveins, outs, dag
  except Exception as e:
    #if not isinstance(e, AssertionError):
    #  print('Error processing', inst)
    #  traceback.print_exc()
    #  exit()
    print(inst)

with open(outf, 'wb') as f:
  pickle.dump(lifted, f)
