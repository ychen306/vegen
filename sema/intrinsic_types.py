from collections import namedtuple

# is is_pointer then this is a pointer to the type
ConcreteType = namedtuple('ConcreteType', ['bitwidth', 'is_float', 'is_double', 'is_pointer'])

IntegerType = lambda bw: ConcreteType(bw, False, False, False)
FloatType = lambda bw: ConcreteType(bw, True, False, False)
DoubleType = lambda bw: ConcreteType(bw, False, True, False)

max_vl = 512

def is_float(type):
  return is_literal(type) or type.is_float or type.is_double

def is_literal(type):
  return type is None

# convert textual types like '_m512i' to ConcreteType
intrinsic_types = {
    '_m512i': IntegerType(512), # typo in the manual
    '__m512i': IntegerType(512),
    '__m256i': IntegerType(256),
    '__m128i': IntegerType(128),
    '__m64': IntegerType(64),

    # single precision floats
    '__m512': FloatType(512),
    '__m256': FloatType(256),
    '__m128': FloatType(128),
    '_m512': FloatType(512),
    '_m256': FloatType(256),
    '_m128': FloatType(128),

    # double precision floats
    '__m512d': DoubleType(512),
    '__m256d': DoubleType(256),
    '__m128d': DoubleType(128),
    '_m512d': DoubleType(512),
    '_m256d': DoubleType(256),
    '_m128d': DoubleType(128),

    # masks
    '__mmask8': IntegerType(8),
    '__mmask16': IntegerType(16),
    '__mmask32': IntegerType(32),
    '__mmask64': IntegerType(64),

    'float': FloatType(32),
    'double': DoubleType(64),
    'int': IntegerType(32),
    'char': IntegerType(8),
    'short': IntegerType(16),
    'unsigned short': IntegerType(16),
    'const int': IntegerType(32),
    'uint': IntegerType(32),
    'unsigned int': IntegerType(32),
    'unsigned char': IntegerType(8),
    'unsigned long': IntegerType(64),
    '__int64': IntegerType(64),
    '__int32': IntegerType(32),
    'unsigned __int32': IntegerType(32),
    'unsigned __int64': IntegerType(64),
    '_MM_PERM_ENUM': IntegerType(8),
    }
