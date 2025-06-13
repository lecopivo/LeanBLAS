import LeanBLAS.FFI.CBLASLevelThreeFloat64
import LeanBLAS.Spec.LevelThree

/-!
# CBLAS Level 3 Implementation

This module provides the CBLAS (C interface to BLAS) implementation of Level 3 BLAS operations
for Float64Array types. Level 3 operations are matrix-matrix operations with O(n³) complexity.

## Overview

Level 3 BLAS operations are the most computationally intensive and benefit the most from
optimized implementations. This module provides:
- General matrix multiplication (GEMM)
- Symmetric matrix operations (SYMM, SYRK, SYR2K)
- Triangular matrix operations (TRMM, TRSM)

## Performance Characteristics

Level 3 operations achieve the highest arithmetic intensity (operations per memory access)
making them ideal for:
- Cache optimization
- Parallel execution
- Vectorization
- GPU acceleration

## Matrix Storage

All matrices use the standard BLAS storage format:
- Matrices stored as 1D arrays with leading dimension parameter
- Support for both row-major and column-major layouts
- Efficient submatrix operations through offset parameters

## Implementation Strategy

The implementation leverages highly optimized BLAS libraries that:
- Use blocking algorithms for cache efficiency
- Employ SIMD instructions for vectorization
- Support multi-threading for large matrices
- Provide architecture-specific optimizations
-/

namespace BLAS.CBLAS

open Sorry

/-- CBLAS implementation of Level 3 BLAS operations for Float64Array.

This instance provides high-performance matrix-matrix operations through FFI
bindings to optimized BLAS libraries. All operations support flexible matrix
layouts and in-place computation for memory efficiency. -/
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
