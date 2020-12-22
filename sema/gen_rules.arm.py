from sig import InputType
from arm_semas import semas
import sys
import pickle
import gen_rules

lifted_f = sys.argv[1]
with open(lifted_f, 'rb') as f:
  lifted = pickle.load(f)

# use a dummy cost model for now
intrin2cost = { intrin : 1 for intrin in lifted.keys() }

bundles = {}
for inst, (_, out_ids, dag) in iter(lifted.items()):
  xs, y, y_ty, _ = semas[inst]
  input_types = [InputType(bitwidth=x.size(), is_constant=False) for x in xs]
  output_sizes = [y_ty.num_elems * y_ty.elem_size]
  sig = input_types, output_sizes
  try:
    print('Emitting pattern for', inst)
    rb = gen_rules.RuleBundle(sig, (xs, y), out_ids, dag)
    if not rb.all_lanes_simple():
      print(inst, 'yucky lanes')
      continue
    if rb.has_nop():
      print(inst, 'has noop lane')
      continue
    bundles[inst] = rb
  except AssertionError as e:
    print(inst, 'assertion error')
    pass

print('Num instructions:', len(bundles))

# dummy features
inst_features = {intrin : [] for intrin in semas.keys()}

with open('InstSema.arm.cpp', 'w') as f:
  f.write('''
#include "InstSema.h"
#include "MatchingUtil.h"

using namespace llvm;
using namespace PatternMatch;
    ''')
  f.write(gen_rules.codegen(bundles, inst_features, intrin2cost, binding_vector_name='ArmInsts'))
