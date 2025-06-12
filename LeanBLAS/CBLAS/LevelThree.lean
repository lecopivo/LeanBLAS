import LeanBLAS.FFI.CBLASLevelThreeFloat64
import LeanBLAS.Spec.LevelThree

namespace BLAS.CBLAS

open Sorry

instance : LevelThreeData Float64Array Float Float where
  gemm order transA transB M N K_dim alpha A offA lda B offB ldb beta C offC ldc := 
    dgemm order transA transB M.toUSize N.toUSize K_dim.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

  symm order side uplo M N alpha A offA lda B offB ldb beta C offC ldc := 
    dsymm order side uplo M.toUSize N.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

  syrk order uplo trans N K_dim alpha A offA lda beta C offC ldc := 
    dsyrk order uplo trans N.toUSize K_dim.toUSize alpha A offA.toUSize lda.toUSize beta C offC.toUSize ldc.toUSize

  syr2k order uplo trans N K_dim alpha A offA lda B offB ldb beta C offC ldc := 
    dsyr2k order uplo trans N.toUSize K_dim.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

  trmm order side uplo transA diag M N alpha A offA lda B offB ldb := 
    dtrmm order side uplo transA diag M.toUSize N.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize

  trsm order side uplo transA diag M N alpha A offA lda B offB ldb := 
    dtrsm order side uplo transA diag M.toUSize N.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize

end BLAS.CBLAS
