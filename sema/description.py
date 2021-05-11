from dataclasses import dataclass
from typing import List
import z3

@dataclass 
class Type:
  bitwidth: int
  ctype: str # the c intrinsic type name
  is_constant: bool = False # is this an immediate?
  effective_width : int = None

@dataclass
class Signature:
  inputs: List[Type]
  output: Type

@dataclass
class Semantics:
  inputs: List[z3.BitVecRef]
  output: z3.BitVecRef

@dataclass
class Instruction:
  name: str
  sig: Signature
  sema: Semantics
  cost: int
  element_size: int # output element
  features: List[str] # CPU features
