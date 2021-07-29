import sys
from tempfile import NamedTemporaryFile
import subprocess

def gen_harnest(num_buffers, template, outf):
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
'''.encode())

  for i in range(num_buffers):
    outf.write(f'int x{i}[1024];\n'.encode())

  buffers = [f'x{i}' for i in range(num_buffers)]

  outf.write('''
int main() {
  srand(42);
'''.encode())

  # initialize the buffers
  for buf in buffers:
    outf.write(f'  init_buffer({buf}, 1024);\n'.encode())

  # run the function on the buffers with user-defined template
  outf.write(f'  {template % tuple(buffers)};\n'.encode())

  for buf in buffers:
    outf.write(f'  print_buffers({buf}, 1024);\n'.encode())
  outf.write('}\n'.encode())

num_buffers, template, ref, test = sys.argv[1:]

with NamedTemporaryFile() as ref_obj,\
    NamedTemporaryFile() as test_obj,\
    NamedTemporaryFile() as ref_exe,\
    NamedTemporaryFile() as test_exe,\
    NamedTemporaryFile() as harnest_obj:
  subprocess.check_output(['llc', ref, '-filetype', 'obj', '-o', ref_obj.name])
  subprocess.check_output(['llc', test, '-filetype', 'obj', '-o', test_obj.name])
  clang = subprocess.Popen(['clang', '-c', '-x', 'c', '-', '-o', harnest_obj.name], stdin=subprocess.PIPE, stderr=subprocess.DEVNULL)
  gen_harnest(int(num_buffers), template, clang.stdin)
  clang.communicate()
  subprocess.check_output(['clang', ref_obj.name, harnest_obj.name, '-o', ref_exe.name])
  subprocess.check_output(['clang', test_obj.name, harnest_obj.name, '-o', test_exe.name])
  ref_out = subprocess.check_output([ref_exe.name], timeout=1)
  test_out = subprocess.check_output([test_exe.name], timeout=1)
  if ref_out != test_out:
    print('incorrect')
    sys.exit(1)
  sys.exit(0)
