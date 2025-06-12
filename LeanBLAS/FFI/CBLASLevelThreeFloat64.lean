import LeanBLAS.FFI.FloatArray
import LeanBLAS.Spec.LevelTwo

namespace BLAS.CBLAS

/-! ## Level 3 BLAS Float64 FFI Declarations -/

-- General matrix-matrix multiplication
-- C := alpha*A*B + beta*C
@[extern "leanblas_cblas_dgemm"]
opaque dgemm (order : Order) (transA : Transpose) (transB : Transpose)
    (M : USize) (N : USize) (K : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize)
    (B : @& Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : Float64Array) (offC : USize) (ldc : USize) : Float64Array

-- Symmetric matrix-matrix multiplication
-- C := alpha*A*B + beta*C  or  C := alpha*B*A + beta*C
@[extern "leanblas_cblas_dsymm"]
opaque dsymm (order : Order) (side : Side) (uplo : UpLo)
    (M : USize) (N : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize)
    (B : @& Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : Float64Array) (offC : USize) (ldc : USize) : Float64Array

-- Symmetric rank-k update
-- C := alpha*A*A^T + beta*C  or  C := alpha*A^T*A + beta*C
@[extern "leanblas_cblas_dsyrk"]
opaque dsyrk (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : USize) (K : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize) (beta : Float)
    (C : Float64Array) (offC : USize) (ldc : USize) : Float64Array

-- Symmetric rank-2k update
-- C := alpha*A*B^T + alpha*B*A^T + beta*C  or  C := alpha*A^T*B + alpha*B^T*A + beta*C
@[extern "leanblas_cblas_dsyr2k"]
opaque dsyr2k (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : USize) (K : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize)
    (B : @& Float64Array) (offB : USize) (ldb : USize) (beta : Float)
    (C : Float64Array) (offC : USize) (ldc : USize) : Float64Array

-- Triangular matrix-matrix multiplication
-- B := alpha*A*B  or  B := alpha*B*A
@[extern "leanblas_cblas_dtrmm"]
opaque dtrmm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : USize) (N : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize)
    (B : Float64Array) (offB : USize) (ldb : USize) : Float64Array

-- Triangular solve with multiple right-hand sides
-- op(A)*X = alpha*B  or  X*op(A) = alpha*B
@[extern "leanblas_cblas_dtrsm"]
opaque dtrsm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : USize) (N : USize) (alpha : Float)
    (A : @& Float64Array) (offA : USize) (lda : USize)
    (B : Float64Array) (offB : USize) (ldb : USize) : Float64Array
