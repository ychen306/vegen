from lift_sema import *
from gen_rules import *
from compiler import compile
from manual_parser import parse_specs
from pprint import pprint
from canonicalize import canonicalize
from fp_sema import set_precision

set_precision(False)

specs = parse_specs('data-latest.xml')

debug = '_mm_dpwssds_epi32'
debug = '_mm256_andnot_pd'
debug = '_mm_packs_epi32'
debug = '_mm256_min_epu16'
debug = '_mm256_min_ps'
debug = '_mm_sad_epu8'
debug = '_mm_srai_epi16'
debug = '_mm_sra_epi16'
if debug:
  translator = Translator()
  _, [y] = compile(specs[debug])
  #y = z3.simplify(y, pull_cheap_ite=True)
  #y = elim_dead_branches(y)
  #y = elim_redundant_branches(y)
  #print(y.children()[-1])
  #exit()

  #y_reduced = reduce_bitwidth(y)
  #z3.prove(y_reduced == y)
  #y = y_reduced

  #outs, dag = translator.translate_formula(y, get_elem_size(specs[debug]))
  #print('typechecked:', typecheck(dag))
  ##print(outs)
  ##pprint(dag)
  #new_dag, new_root = canonicalize(dag, outs[0])
  #pprint(new_dag)
  #print(new_root)
  #exit()
  #print(outs)
  #pprint(dag)
  #bo = BoundOperation(outs[-1], dag)
  #print(bo.get_matching_code())
