import subprocess
from tempfile import NamedTemporaryFile
import sys
import multiprocessing

def save_bad_src(src, fname='bad.c'):
  with open(fname, 'wb') as outf:
    outf.write(src)

default_outdir = 'buggy_c_files'
def run_csmith(seed, outdir=default_outdir):
  print('testing seed', seed)
  src = subprocess.check_output(['csmith', '--seed', str(seed), '--no-volatiles', '--no-volatile-pointers'], stderr=subprocess.DEVNULL)
  with NamedTemporaryFile(suffix='.c') as src_f\
      , NamedTemporaryFile() as clang_exe\
      , NamedTemporaryFile() as vegen_exe:
    src_f.write(src)
    src_f.flush()
    subprocess.check_call(['clang', src_f.name, '-O3', '-o', clang_exe.name, '-I/usr/local/include/csmith-2.3.0/'], stderr=subprocess.DEVNULL)
    try:
      clang_out = subprocess.check_output([clang_exe.name], stderr=subprocess.DEVNULL, timeout=1)
    except subprocess.TimeoutExpired:
      print('clang binary timed out, seed =', seed)
      return
  
    try:
      subprocess.check_output(['vegen-clang', src_f.name, '-O3', '-mllvm',
      '-test-codegen', '-o', vegen_exe.name, '-I/usr/local/include/csmith-2.3.0/'], stderr=subprocess.DEVNULL)
    except:
      save_bad_src(src, outdir+'/'+str(seed)+'.c')
      print('vegen failed at compile time, seed =', seed)
    try:
      vegen_out = subprocess.check_output([vegen_exe.name], timeout=1)
    except subprocess.TimeoutExpired:
      save_bad_src(src, outdir+'/'+str(seed)+'.c')
      print('vegen binary timed out, seed =', seed)
      return
  
    if clang_out != vegen_out:
      save_bad_src(src, outdir+'/'+str(seed)+'.c')
      print('Found bug in VeGen, seed =', seed)
      return
    else:
      print('VeGen seems correct, seed =', seed )
      return

if __name__ == '__main__':
  import itertools
  seeds = itertools.count(0)
  p = multiprocessing.Pool(8)
  for s in seeds:
    p.apply_async(run_csmith, (s,))
