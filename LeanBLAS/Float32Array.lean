import LeanBLAS.Util

namespace BLAS

open Sorry

set_option linter.unusedVariables false

structure Float32Array where
  data : ByteArray
  h_size : data.size % 4 = 0

structure Float64Array where
  data : ByteArray
  h_size : data.size % 8 = 0

structure ComplexFloat32Array where
  data : ByteArray
  h_size : data.size % 8 = 0

structure ComplexFloat64Array where
  data : ByteArray
  h_size : data.size % 16 = 0

instance : Inhabited Float32Array := ⟨.mkEmpty 0, sorry_proof⟩
instance : Inhabited Float64Array := ⟨.mkEmpty 0, sorry_proof⟩
instance : Inhabited ComplexFloat32Array := ⟨.mkEmpty 0, sorry_proof⟩
instance : Inhabited ComplexFloat64Array := ⟨.mkEmpty 0, sorry_proof⟩


def Float32Array.size (a : Float32Array) := a.data.size / 4
def Float64Array.size (a : Float64Array) := a.data.size / 8
