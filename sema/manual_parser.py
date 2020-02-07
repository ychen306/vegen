from sema_ast import Parameter, Spec
from parser import parse

std_funcs = '''
DEFINE MIN(a, b) {
    return a < b ? a : b
}
DEFINE MAX(a, b) {
    return a > b ? a : b
}
'''

def get_spec_from_xml(node):
  params = []
  for param_node in node.findall('parameter'):
    name = param_node.attrib['varname']
    type = param_node.attrib['type']
    if name == '':
      continue
    params.append(Parameter(name, type))
  intrin = node.attrib['name']
  inst = node.find('instruction')
  inst_form = inst.attrib.get('form', '')
  assert(inst is not None)
  operation = node.find('operation')
  assert(operation is not None)
  spec, binary_exprs = parse(std_funcs+operation.text)
  rettype = node.attrib['rettype']
  return Spec(
      intrin=intrin,
      inst=inst,
      spec=spec,
      params=params,
      rettype=rettype,
      configs={}, # by default nothing is configured
      inst_form=inst_form,
      binary_exprs=binary_exprs)
