import LeanBLAS.ComplexFloat

/-!
# Float Array Types for BLAS FFI

This module defines array types for floating-point numbers that are compatible with
BLAS C interfaces. These types serve as the foundation for all BLAS operations in Lean.

## Design Philosophy

Instead of using Lean's native `Array Float`, we use `ByteArray` wrappers to ensure:
- Direct memory layout compatibility with C arrays
- Zero-copy FFI calls to BLAS libraries
- Proper alignment for SIMD operations
- Efficient memory management

## Type Safety

Each array type includes a proof that the underlying byte array has the correct size
(multiple of element size), ensuring type safety at the Lean level while maintaining
C compatibility.

## Array Types

- `Float32Array`: Single-precision real numbers (4 bytes per element)
- `Float64Array`: Double-precision real numbers (8 bytes per element)
- `ComplexFloat32Array`: Single-precision complex numbers (8 bytes per element)
- `ComplexFloat64Array`: Double-precision complex numbers (16 bytes per element)
-/

namespace BLAS

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

/-- Convert a Lean FloatArray to Float64Array for BLAS operations.
    This is a zero-copy operation that reinterprets the memory layout. -/
@[extern "leanblas_float_array_to_byte_array"]
opaque _root_.FloatArray.toFloat64Array (a : FloatArray) : Float64Array

/-- Convert a Float64Array back to Lean's FloatArray.
    This is a zero-copy operation that reinterprets the memory layout. -/
@[extern "leanblas_byte_array_to_float_array"]
opaque Float64Array.toFloatArray (a : Float64Array) : FloatArray

/-- Convenient syntax for creating Float64Arrays from literals.
    Example: `#f64[1.0, 2.0, 3.0]` creates a Float64Array with three elements. -/
macro "#f64[" xs:term,* "]" : term => `((FloatArray.mk #[$xs,*]).toFloat64Array)

/-- Convert a Lean ComplexFloatArray to ComplexFloat64Array for BLAS operations.
    This maps the interleaved real/imaginary format to the BLAS-compatible layout. -/
@[extern "leanblas_complex_float_array_to_byte_array"]
opaque _root_.ComplexFloatArray.toComplexFloat64Array (a : ComplexFloatArray) : ComplexFloat64Array

/-- Convert a ComplexFloat64Array back to Lean's ComplexFloatArray.
    This reverses the layout transformation for use in Lean code. -/
@[extern "leanblas_byte_array_to_complex_float_array"]
opaque ComplexFloat64Array.toComplexFloatArray (a : ComplexFloat64Array) : ComplexFloatArray

/-- Convenient syntax for creating ComplexFloat64Arrays from literals.
    Example: `#c64[⟨1.0, 2.0⟩, ⟨3.0, 4.0⟩]` creates a ComplexFloat64Array with two complex numbers. -/
macro "#c64[" xs:term,* "]" : term => `((ComplexFloatArray.mk #[$xs,*]).toComplexFloat64Array)
