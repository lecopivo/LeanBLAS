import LeanBLAS.FFI.FloatArray

namespace BLAS.CBLAS

open BLAS

set_option linter.unusedVariables false

instance : Nonempty BLAS.Float64Array := ⟨BLAS.Float64Array.mk (.emptyWithCapacity 0) (by decide)⟩

/-- dgemm
inputs: alpha, A, B, beta, C
outputs: C with the matrix-matrix product
-/
@[extern "leanblas_cblas_dgemm"]
opaque dgemm (order : UInt8) (transA : UInt8) (transB : UInt8) (M : USize) (N : USize) (K : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize)
    (B : @& BLAS.Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : BLAS.Float64Array) (offC : USize) (ldc : USize) : BLAS.Float64Array

/-- dsymm
inputs: alpha, A, B, beta, C
outputs: C updated
-/
@[extern "leanblas_cblas_dsymm"]
opaque dsymm (order : UInt8) (side : UInt8) (uplo : UInt8) (M : USize) (N : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize)
    (B : @& BLAS.Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : BLAS.Float64Array) (offC : USize) (ldc : USize) : BLAS.Float64Array

/-- dtrmm
inputs: alpha, A, B
outputs: B updated
-/
@[extern "leanblas_cblas_dtrmm"]
opaque dtrmm (order : UInt8) (side : UInt8) (uplo : UInt8) (transA : UInt8) (diag_enum : UInt8) (M : USize) (N : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize)
    (B : BLAS.Float64Array) (offB : USize) (ldb : USize) : BLAS.Float64Array

/-- dtrsm
inputs: alpha, A, B
outputs: B replaced by solution X
-/
@[extern "leanblas_cblas_dtrsm"]
opaque dtrsm (order : UInt8) (side : UInt8) (uplo : UInt8) (transA : UInt8) (diag_enum : UInt8) (M : USize) (N : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize)
    (B : BLAS.Float64Array) (offB : USize) (ldb : USize) : BLAS.Float64Array

/-- dsyrk
inputs: alpha, A, beta, C
outputs: C updated
-/
@[extern "leanblas_cblas_dsyrk"]
opaque dsyrk (order : UInt8) (uplo : UInt8) (trans : UInt8) (N : USize) (K : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize) (beta : Float)
    (C : BLAS.Float64Array) (offC : USize) (ldc : USize) : BLAS.Float64Array

/-- dsyr2k
inputs: alpha, A, B, beta, C
outputs: C updated
-/
@[extern "leanblas_cblas_dsyr2k"]
opaque dsyr2k (order : UInt8) (uplo : UInt8) (trans : UInt8) (N : USize) (K : USize) (alpha : Float)
    (A : @& BLAS.Float64Array) (offA : USize) (lda : USize)
    (B : @& BLAS.Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : BLAS.Float64Array) (offC : USize) (ldc : USize) : BLAS.Float64Array

end BLAS.CBLAS
