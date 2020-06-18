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
'''

def parse_cpuid(cpuid):
  cpuid = cpuid.text.lower().replace('_', '')
  if '/' in cpuid:
    return cpuid.split('/')[0]
  return cpuid

def get_spec_from_xml(node):
  params = []
  for param_node in node.findall('parameter'):
    name = param_node.attrib['varname']
    type = param_node.attrib['type']
    if name == '':
      continue
    params.append(Parameter(name, type))
  cpuids = [parse_cpuid(cpuid) for cpuid in node.findall('CPUID')]
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
      inst=inst.attrib.get('name'),
      spec=spec,
      params=params,
      rettype=rettype,
      cpuids=cpuids,
      configs={}, # by default nothing is configured
      inst_form=inst_form,
      binary_exprs=binary_exprs)


def parse_specs(spec_f):
  specs = {}
  
  for intrin in ET.parse(spec_f).iter('intrinsic'):
    try:
      spec = get_spec_from_xml(intrin)
      specs[spec.intrin] = spec
    except:
      continue
  return specs
