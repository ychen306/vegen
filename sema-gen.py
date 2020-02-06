import xml.etree.ElementTree as ET
from manual_parser import get_spec_from_xml
import sys
from interp import interpret
from spec_configurer import configure_spec
from compiler import compile
from spec_serializer import dump_spec

data_f, out_fname = sys.argv[1:]
data_root = ET.parse(data_f)

num_parsed = 0
num_skipped = 0
supported_insts = set()
skipped_insts = set()

num_ok = 0
num_interpreted = 0

skipped = False
skip_to = '_mm512_popcnt_epi16'
skip_to = None

outf = open(out_fname, 'w')

for intrin in data_root.iter('intrinsic'):
  cpuid = intrin.find('CPUID')
  sema = intrin.find('operation') 
  inst = intrin.find('instruction')
  inst_form = None
  if inst is None:
    continue
  inst_form = inst.attrib['name'], inst.attrib.get('form')
  cpuid_text = 'Unknown'
  if cpuid is not None:
    if cpuid.text in ('MMX', 'AES', 'SHA', 'MPX', 'KNCNI', 
        'AVX512_4FMAPS', 'AVX512_BF16',
        'INVPCID', 'RTM', 'XSAVE', 
        'FSGSBASE', 'RDRAND', 'RDSEED'):
      continue
    cpuid_text = cpuid.text

  if (intrin.attrib['name'].endswith('getcsr') or
      intrin.attrib['name'].endswith('setcsr') or
      '_cmp_' in intrin.attrib['name'] or
      'zeroall' in intrin.attrib['name'] or
      'zeroupper' in intrin.attrib['name'] or
      intrin.attrib['name'] == '_mm_sha1rnds4_epu32' or
      'mant' in intrin.attrib['name'] or
      'ord' in intrin.attrib['name'] or
      '4dpwss' in intrin.attrib['name'] or
      'cvt' in intrin.attrib['name'] or
      intrin.attrib['name'].startswith('_bit') or
      intrin.attrib['name'] in ('_rdpmc', '_rdtsc')):
    continue
  cat = intrin.find('category')
  if cat is not None and cat.text in (
      'Elementary Math Functions', 
      'General Support', 
      'Load', 'Store', 'Special Math Functions'):
    continue
  if skip_to is not None and not skipped:
    if intrin.attrib['name'] != skip_to:
      continue
    else:
      skipped = True
  if sema is not None and (
      'MEM' in sema.text or
      'FP16' in sema.text or
      'Float16' in sema.text or
      'MOD2' in sema.text or
      'affine_inverse_byte' in sema.text or
      'ShiftRows' in sema.text or
      'MANTISSA' in sema.text or
      'ConvertExpFP' in sema.text or
      '<<<' in sema.text or
      ' MXCSR ' in sema.text or
      'ZF' in sema.text or
      'CF' in sema.text or
      'NaN' in sema.text or 
      'CheckFPClass' in sema.text or
      'ROUND' in sema.text or
      'carry_out' in sema.text or
      'SignBit' in sema.text or
      'SSP' in sema.text):
    continue
  if 'str' in intrin.attrib['name']:
    if inst is not None:
      skipped_insts.add(inst_form)
    num_skipped += 1
    continue

  if 'fixup' in intrin.attrib['name']:
    if inst is not None:
      skipped_insts.add(inst_form)
    num_skipped += 1
    continue
  if 'round' in intrin.attrib['name']:
    if inst is not None:
      skipped_insts.add(inst_form)
    num_skipped += 1
    continue
  if 'prefetch' in intrin.attrib['name']:
    if inst is not None:
      skipped_insts.add(inst_form)
    num_skipped += 1
    continue

  print(intrin.attrib['name'], cpuid_text, num_parsed, flush=True)
  if inst is not None and sema is not None:
    try:
      #if 'ELSE IF' in sema.text:
      #  continue
      spec = get_spec_from_xml(intrin)
      ok, compiled, new_spec = configure_spec(spec, num_tests=100)
      if ok:
        spec_sema = dump_spec(new_spec, precision=False)
        outf.write(intrin.attrib['name'] + '\n')
        outf.write(spec_sema + '\n')
        outf.flush()
      num_interpreted += compiled
      num_ok += ok
      print('\t',ok, num_ok,'/', num_interpreted, flush=True)
      supported_insts.add(inst_form)
      num_parsed += 1
    except SyntaxError:
      print('Parsed', num_parsed, ' semantics, failling:')
      print(sema.text)
      print(intrin.attrib['name'])
      break

outf.close()

print('Parsed:', num_parsed,
    'Skipped:', num_skipped,
    'Num unique inst forms parsed:', len(supported_insts),
    'Num inst forms skipped:', len(skipped_insts)
    )
