import sys
from tempfile import NamedTemporaryFile
import subprocess

def gen_harnest(decl, num_buffers, template, outf):
  outf.write('''#include <stdio.h>
#include <stdlib.h>

void print_buffers(int *x, int n) {
  for (int i = 0; i < n; i++)
    printf("%d ", x[i]);
  printf("\\n");
}

void init_buffer(int *x, int n) {
  for (int i = 0; i < n; i++)
    x[i] = rand();
}
''')

  for i in range(num_buffers):
    outf.write(f'int x{i}[1024];\n')

  buffers = [f'x{i}' for i in range(num_buffers)]
  outf.write(decl+';\n');

  outf.write('''
int main() {
  srand(42);
''')

  # initialize the buffers
  for buf in buffers:
    outf.write(f'  init_buffer({buf}, 1024);\n')

  # run the function on the buffers with user-defined template
  outf.write(f'  {template % tuple(buffers)};\n')

  for buf in buffers:
    outf.write(f'  print_buffers({buf}, 1024);\n')
  outf.write('}\n')

num_buffers, decl, template, ref, test = sys.argv[1:]

with NamedTemporaryFile() as test_exe,\
    NamedTemporaryFile() as ref_exe,\
    NamedTemporaryFile() as ref_obj,\
    NamedTemporaryFile() as test_obj,\
    NamedTemporaryFile(mode='w') as harnest_src,\
    NamedTemporaryFile() as harnest_obj:

  gen_harnest(decl, int(num_buffers), template, harnest_src)
  harnest_src.flush()

  subprocess.check_call(['cc', '-c', '-x', 'c', harnest_src.name, '-o', harnest_obj.name])
  subprocess.check_call(['llc', ref, '-filetype=obj', '-o', ref_obj.name])
  subprocess.check_call(['llc', test, '-filetype=obj', '-o', test_obj.name])
  subprocess.check_call(['cc', harnest_obj.name, ref_obj.name, '-o', ref_exe.name])
  subprocess.check_call(['cc', harnest_obj.name, test_obj.name, '-o', test_exe.name])

  ref_out = subprocess.check_output([ref_exe.name], timeout=1)
  test_out = subprocess.check_output([test_exe.name], timeout=1)
  if ref_out != test_out:
    print('incorrect')
    sys.exit(1)
  sys.exit(0)
