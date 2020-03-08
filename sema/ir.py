from collections import namedtuple
import z3

Instruction = namedtuple('Instruction', ['op', 'bitwidth', 'args'])
Constant = namedtuple('Constant', ['value', 'bitwidth'])

class DynamicSlice:
  def __init__(self, base, idx, stride):
    self.base = base.decl().name()
    self.base_size = base.size()
    self.idx = idx
    self.stride = stride
    self.bitwidth = stride
    self.hash_key = self.base, idx, stride

  def __hash__(self):
    return hash(self.hash_key)

  def __eq__(self, other):
    return self.hash_key == other.hash_key

  def __repr__(self):
    return f'choose<{self.stride}>({self.base}).at({self.idx})'

  def get_z3_base(self):
    return z3.BitVec(self.base, self.base_size)

  def size(self):
    return self.stride

class Mux:
  def __init__(self, ctrl, keys, values, bitwidth):
    self.ctrl = ctrl
    self.kv_pairs = tuple(sorted(zip(keys, values)))
    self.bitwidth = bitwidth

  def __hash__(self):
    return hash(self.kv_pairs)

  def __eq__(self, other):
    return self.kv_pairs == other.kv_pairs

  def __repr__(self):
    mapping = ', '.join(f'{k} -> {v}' for k, v in self.kv_pairs)
    return f'Mux[{self.ctrl}]({mapping})'

class Slice:
  def __init__(self, base, lo, hi):
    '''
    lo is inclusive and hi is exclusive
    '''
    self.base = base.decl().name()
    self.base_size = base.size()
    self.lo = lo
    self.hi = hi
    self.hash_key = self.base, lo, hi

  def get_z3_base(self):
    return z3.BitVec(self.base, self.base_size)

  def __hash__(self):
    return hash(self.hash_key)

  def __eq__(self, other):
    return self.hash_key == other.hash_key

  def overlaps(self, other):
    return (
        self.base == other.base and
        self.size() + other.size() > self.union(other).size())

  def union(self, other):
    assert self.base == other.base
    lo = min(self.lo, other.lo)
    hi = max(self.hi, other.hi)
    return Slice(self.get_z3_base(), lo, hi)

  def size(self):
    return self.hi - self.lo

  @property
  def bitwidth(self):
    return self.size()

  def to_z3(self):
    return z3.Extract(self.hi-1, self.lo, self.get_z3_base())

  def __repr__(self):
    return f'{self.base}[{self.lo}:{self.hi}]'

class Insert:
  def __init__(self, src, src_size, x, idx):
    '''
    replace src[idx] with x
    '''
    self.src = src
    self.src_size = src_size
    self.x = x
    self.idx = idx

  @property
  def bitwidth(self):
    return self.src_size

  def __repr__(self):
    return f'replace {self.src} at {self.idx} with {self.x}'

ir_types = (Constant, Instruction, Slice, DynamicSlice, Mux, Insert)

binary_ops = {
        'Add', 'Sub', 'Mul', 'SDiv', 'SRem',
        'UDiv', 'URem', 'Shl', 'LShr', 'AShr',
        'And', 'Or', 'Xor',

        'FAdd', 'FSub', 'FMul', 'FDiv', 'FRem',
        }

commutative_binary_ops = {
        'Add', 'Mul',
        'And', 'Or', 'Xor',

        'FAdd', 'FMul',
        }
icmp_ops = {
        'Eq', 'Ne', 'Ugt', 'Uge', 'Ult', 'Ule', 'Sgt', 'Sge', 'Slt', 'Sle',
        }
fcmp_ops = {
        'Foeq', 'Fone', 'Fogt', 'Foge', 'Folt', 'Fole',
        }
cmp_ops = icmp_ops.union(fcmp_ops)
