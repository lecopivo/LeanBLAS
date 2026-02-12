import LeanBLAS.Spec.LevelThree
import LeanBLAS.FFI.CBLASLevelThreeFloat64

namespace BLAS.CBLAS

instance : BLAS.LevelThreeData BLAS.Float64Array Float Float where

  gemm order transA transB M N K alpha A offA lda B offB ldb beta C offC ldc :=
    dgemm order.toUInt8 transA.toUInt8 transB.toUInt8 M.toUSize N.toUSize K.toUSize alpha
      A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

  symm order side uplo M N alpha A offA lda B offB ldb beta C offC ldc :=
    dsymm order.toUInt8 side.toUInt8 uplo.toUInt8 M.toUSize N.toUSize alpha
      A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

  trmm order side uplo transA diag M N alpha A offA lda B offB ldb :=
    dtrmm order.toUInt8 side.toUInt8 uplo.toUInt8 transA.toUInt8 diag.toUInt8 M.toUSize N.toUSize alpha
      A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize

  trsm order side uplo transA diag M N alpha A offA lda B offB ldb :=
    dtrsm order.toUInt8 side.toUInt8 uplo.toUInt8 transA.toUInt8 diag.toUInt8 M.toUSize N.toUSize alpha
      A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize

  syrk order uplo trans N K alpha A offA lda beta C offC ldc :=
    dsyrk order.toUInt8 uplo.toUInt8 trans.toUInt8 N.toUSize K.toUSize alpha
      A offA.toUSize lda.toUSize beta C offC.toUSize ldc.toUSize

  syr2k order uplo trans N K alpha A offA lda B offB ldb beta C offC ldc :=
    dsyr2k order.toUInt8 uplo.toUInt8 trans.toUInt8 N.toUSize K.toUSize alpha
      A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

end BLAS.CBLAS
