import z3
from collections import namedtuple, defaultdict
from ir import *

# Label the stride at which input bitvectors are sliced,
# and which input is the control/index parameter, if any
SwizzleInfo = namedtuple('ShuffleInfo', ['stride', 'parameters'])

def get_swizzle_info(lifted):
  '''
  analyze the lifted semantics of an instruction
  return SwizzleInfo for that instruction

  return None if the instruction slices some input
  with more than one stride (ignoring control or index parameters)
  '''
  _, out_ids, dag = lifted
  # mapipng argument -> their slices
  slices = defaultdict(list)
  parameters = set()
  for v in dag.values():
    if isinstance(v, DynamicSlice):
      idx = dag[v.idx]
      assert(isinstance(idx, Slice))
      parameters.add(idx.get_z3_base())
      slices[v.get_z3_base()].append(v)
    elif isinstance(v, Mux):
      ctrl = dag[v.ctrl]
      assert(isinstance(ctrl, Slice))
      parameters.add(ctrl.get_z3_base())
    elif isinstance(v, Slice):
      slices[v.get_z3_base()].append(v)

  # make sure there is a single stride
  sizes = set()
  for arg in slices:
    # ignore the parameter
    if arg in parameters:
      continue
    for s in slices[arg]:
      sizes.add(s.size())
  if len(sizes) != 1:
    return None
  size = sizes.pop()

  # FIXME: verify that the output has the same stride

  return SwizzleInfo(size, list(parameters))

def popcount(x):
  count = 0
  for i in range(x.size()):
    count += z3.ZeroExt(31, z3.Extract(i, i, x))
  return count

def get_num_propagated_elements(x, x_stride, args, y):
  '''
  Calculate, symbolically, the max number of elements of x 
  that could be propagated to y,
  assuming y is a swizzle instruction
  '''
  assert(x.size() % x_stride == 0)
  num_elems = x.size() // x_stride
  # assigning a unique id (starting from 1) for each of the lane
  x_val = z3.Concat([z3.BitVecVal(i+1, x_stride) for i in range(num_elems)])
  # assigning the rest of the input 0
  vals = [z3.BitVecVal(0, arg.size()) if arg.get_id() != x.get_id() else x_val
      for arg in args]
  out = z3.simplify(z3.substitute(y, *zip(args, vals)))
  # bitvector representing surviving elements of x
  bv = 0
  for i in range(0, y.size(), x_stride):
    y_elem = z3.Extract(i+x_stride-1, i, out)
    if y_elem.size() < num_elems:
      y_elem = z3.ZeroExt(num_elems-y_elem.size(), y_elem)
    else:
      y_elem = z3.Extract(num_elems-1, 0, y_elem)
    # convert the lane id to its one-hot encoding
    bv = bv | (1 << (y_elem-1))
  return z3.simplify(popcount(bv))

def get_abstract_swizzle_output(inst, lifted, sema, swizzle_info):
  '''
  Given a swizzle instruction of input X = {x_1, ... x_n}, (excluding control parameter)
  (suppose it has only one output), we can assign its output a type:
  Further assume that all x_i are indexed with the same stride
  [a_1, ..., a_n], where
  a_i can have the following type:
    | AtMost c (the instruction can select at most c values from x_1)
    | Exactly c (the instruction can select at exactly c values from x_1)

  return ([a_1, ..., a_n])
  '''
  _, out_ids, dag = lifted

if __name__ == '__main__':
  import sys
  import pickle
  from semas import 

  lifted_f = sys.argv[1]
  with open(lifted_f, 'rb') as f:
    lifted_insts = pickle.load(f)

  for inst, lifted in lifted_insts.items():
    si = get_swizzle_info(lifted)
    if si is None:
      print(inst)
