import LeanBLAS.Util

namespace BLAS

open Sorry

set_option linter.unusedVariables false

/-- Type synonym for `ByteArray` that should be considered as array of `Float32`. -/
structure Float32Array where
  data : ByteArray
  h_size : data.size % 4 = 0

/-- Type synonym for `ByteArray` that should be considered as array of `Float64`. -/
structure Float64Array where
  data : ByteArray
  h_size : data.size % 8 = 0

/-- Type synonym for `ByteArray` that should be considered as array of `ComplexFloat32`. -/
structure ComplexFloat32Array where
  data : ByteArray
  h_size : data.size % 8 = 0

/-- Type synonym for `ByteArray` that should be considered as array of `ComplexFloat`. -/
structure ComplexFloat64Array where
  data : ByteArray
  h_size : data.size % 16 = 0

instance : Inhabited Float32Array := ⟨.emptyWithCapacity 0, by decide⟩
instance : Inhabited Float64Array := ⟨.emptyWithCapacity 0, by decide⟩
instance : Inhabited ComplexFloat32Array := ⟨.emptyWithCapacity 0, by decide⟩
instance : Inhabited ComplexFloat64Array := ⟨.emptyWithCapacity 0, by decide⟩


def Float32Array.size (a : Float32Array) := a.data.size / 4
def Float64Array.size (a : Float64Array) := a.data.size / 8
def ComplexFloat32Array.size (a : ComplexFloat32Array) := a.data.size / 8
def ComplexFloat64Array.size (a : ComplexFloat64Array) := a.data.size / 16


@[extern "leanblas_float_array_to_byte_array"]
opaque _root_.FloatArray.toFloat64Array (a : FloatArray) : Float64Array

@[extern "leanblas_byte_array_to_float_array"]
opaque Float64Array.toFloatArray (a : Float64Array) : FloatArray


macro "#f64[" xs:term,* "]" : term => `((FloatArray.mk #[$xs,*]).toFloat64Array)
