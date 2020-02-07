from bitstring import BitArray, Bits

def int_to_bits(x, bitwidth=32):
  if x < 0:
    return Bits(int=x, length=bitwidth)
  return Bits(uint=x, length=bitwidth)

def float_to_bits(x, bitwidth=32):
  return Bits(float=x, length=bitwidth)

def float_vec_to_bits(vec, float_size=64):
  bitwidth = len(vec) * float_size
  bits = BitArray(uint=0, length=bitwidth)
  for i, x in enumerate(vec):
    update_bits(bits, i*float_size, (i+1)*float_size, float_to_bits(x, float_size))
  return Bits(uint=bits.uint, length=bitwidth)

def bits_to_float_vec(bits, float_size=64):
  vec = []
  for i in range(0, bits.length, float_size):
    vec.append(slice_bits(bits, i, i+float_size).float)
  return vec

def bits_to_long_vec(bits):
  vec = []
  for i in range(0, bits.length, 64):
    vec.append(slice_bits(bits, i, i+64).uint)
  return vec

# this is to deal with the facts that in bitstring, 
# b[0] actually means the HIGHEST ORDER BIT!!!
# DONT TRY TO UPDATE THINGS FROM BITSTRING DIRECTLY
def slice_bits(bits, lo, hi):
  lo, hi = bits.length - hi, bits.length - lo
  return bits[lo:hi]

def update_bits(bits, lo, hi, val):
  lo, hi = bits.length - hi, bits.length - lo
  bits[lo:hi] = val
