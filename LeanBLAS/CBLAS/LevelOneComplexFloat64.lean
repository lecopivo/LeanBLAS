import LeanBLAS.ComplexFloat
import LeanBLAS.Spec.LevelOne

namespace BLAS


/-- zdot (complex dot product)

summary: computes the dot product of two complex vectors

inputs:
- N: the number of elements in the vectors
- X: the first complex vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second complex vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs:
- the dot product of X and Y
-/
@[extern "leanblas_cblas_zdot"]
opaque zdot (N : USize) (X : @& ComplexFloatArray) (offX incX : USize) (Y : @& ComplexFloatArray) (offY incY : USize) : ComplexFloat
