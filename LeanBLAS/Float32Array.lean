namespace BLAS

set_option linter.unusedVariables false

structure Float32Array where
  data : ByteArray
  h_size : data.size % 4 = 0

def Float32Array.size (a : Float32Array) := a.data.size / 4

def Float32Array.uget (a : Float32Array) (i : USize) (h : i.toNat < a.size) := a.data.size / 4
