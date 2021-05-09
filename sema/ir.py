from collections import namedtuple
import z3

Instruction = namedtuple('Instruction', ['op', 'bitwidth', 'args'])
Constant = namedtuple('Constant', ['value', 'bitwidth'])
FPConstant = namedtuple('FPConstant', ['value', 'bitwidth'])

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

ir_types = (Constant, Instruction, Slice)

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

inverted_cmp_ops = {
    'Eq': 'Ne',
    'Ne': 'Eq',
    'Ugt': 'Ult',
    'Uge': 'Ule',
    'Ult': 'Ugt', 
    'Ule': 'Uge',
    'Sgt': 'Slt',
    'Sge': 'Sle',
    'Slt': 'Sgt',
    'Sle': 'Sge',
    'Foeq': 'Fone',
    'Fone': 'Foeq',
    'Fogt': 'Folt',
    'Foge': 'Fole',
    'Folt': 'Fogt',
    'Fole': 'Foge'
    }

cmp_ops = icmp_ops.union(fcmp_ops)
