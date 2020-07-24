from sema_ast import Parameter, Spec
from parser import parse
import xml.etree.ElementTree as ET

std_funcs = '''
DEFINE MIN(a, b) {
  return a < b ? a : b
}
DEFINE MAX(a, b) {
  return a > b ? a : b
}
DEFINE ABS(x) {
  return x >= 0 ? x : -x
}
'''

def parse_cpuid(cpuid):
  cpuid = cpuid.text.lower().replace('_', '')
  if '/' in cpuid:
    return cpuid.split('/')[0]
  return cpuid

def get_spec_from_xml(node):
  params = []
  imm_width = None
  for param_node in node.findall('parameter'):
    name = param_node.attrib.get('varname', '')
    type = param_node.attrib['type']
    if name == '':
      continue
    is_signed = param_node.attrib.get('etype', '').startswith('SI')
    is_imm = param_node.attrib.get('etype') == 'IMM'
    if is_imm:
      imm_width = int(param_node.attrib.get('immwidth', '8'))
    params.append(Parameter(name, type, is_signed, is_imm))
  cpuids = [parse_cpuid(cpuid) for cpuid in node.findall('CPUID')]
  intrin = node.attrib['name']
  inst = node.find('instruction')
  inst_form = inst.attrib.get('form', '')
  assert(inst is not None)
  operation = node.find('operation')
  assert(operation is not None)
  spec, binary_exprs = parse(std_funcs+operation.text)
  output = node.find('return')
  assert(output is not None)
  rettype = output.attrib['type']
  elem_type = output.attrib['etype']
  xed = inst.attrib.get('xed')
  return Spec(
      intrin=intrin,
      inst=inst.attrib.get('name'),
      spec=spec,
      params=params,
      rettype=rettype,
      cpuids=cpuids,
      configs={}, # by default nothing is configured
      inst_form=inst_form,
      imm_width=imm_width,
      elem_type=elem_type,
      xed=xed,
      binary_exprs=binary_exprs)


def parse_specs(spec_f):
  specs = {}
  
  for intrin in ET.parse(spec_f).iter('intrinsic'):
    try:
      spec = get_spec_from_xml(intrin)
      specs[spec.intrin] = spec
    except Exception as e:
      continue
  return specs
