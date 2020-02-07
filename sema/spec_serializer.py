import z3
from z3_utils import *
from compiler import compile
from fp_sema import set_precision, get_precision
import operator
import json

# TODO: rename spec to sema for consistency
def dump_spec(spec, precision=True):
  # FIXME: modify this to mark which input must be compile time constant
  orig_precision = get_precision()
  set_precision(precision)
  param_vals, outs = compile(spec)
  s = z3.Solver()
  for out in outs:
    s.add(out == 0)
  dummy_bench = s.to_smt2()
  dumped = {}
  dumped['inputs'] = [(p.decl().name(), p.size()) for p in param_vals]
  dumped['dummy_bench'] = dummy_bench
  set_precision(orig_precision)
  return json.dumps(dumped)

def load_spec(dumped):
  dumped = json.loads(dumped)
  param_vals = [z3.BitVec(var, size) for var, size in dumped['inputs']]
  outs = []
  s = z3.Solver()
  s.from_string(dumped['dummy_bench'])
  for a in s.assertions():
    outs.append(a.children()[0])
  return param_vals, outs
