import LeanBLAS.FFI.CBLASLevelTwoFloat64
import LeanBLAS.Spec.LevelTwo

/-!
# CBLAS Level 2 Implementation

This module provides the CBLAS (C interface to BLAS) implementation of Level 2 BLAS operations
for Float64Array types. Level 2 operations are matrix-vector operations with O(n²) complexity.

## Overview

The implementation covers all standard Level 2 BLAS operations including:
- General, symmetric, and triangular matrix-vector products
- Rank-1 and rank-2 updates
- Triangular solves
- Banded and packed matrix operations

## Matrix Storage Formats

The implementation supports multiple matrix storage formats:
- **General matrices**: Full storage in row-major or column-major order
- **Symmetric matrices**: Only upper or lower triangle stored
- **Triangular matrices**: Only non-zero triangle stored
- **Banded matrices**: Only diagonals within bandwidth stored
- **Packed matrices**: Triangular/symmetric matrices in compact 1D array

## Implementation Details

All operations use FFI bindings to optimized BLAS libraries. The module handles:
- Layout conversion (row-major vs column-major)
- Index transformation (Nat to USize)
- Transpose and conjugate operations
- Proper memory access patterns for cache efficiency
-/

namespace BLAS.CBLAS

/-- CBLAS implementation of Level 2 BLAS operations for Float64Array.

This instance provides efficient matrix-vector operations through FFI calls
to optimized BLAS libraries. All matrix storage formats (general, symmetric,
triangular, banded, packed) are supported with appropriate layout parameters. -/
instance : LevelTwoData Float64Array Float Float where

  gemv order trans M N a A offA ldaA X offX incX b Y offY incY :=
    dgemv order trans M.toUSize N.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  bmv order trans M N KL KU a A offA ldaA X offX incX b Y offY incY :=
    dbmv order trans M.toUSize N.toUSize KL.toUSize KU.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  trmv order uplo trans diag N A offA lda X offX incX :=
    dtrmv order uplo trans diag N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbmv order uplo trans diag N K A offA lda X offX incX :=
    dtbmv order uplo trans diag N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpmv order uplo trans diag N A offA X offX incX :=
    dtpmv order uplo trans diag N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  trsv order uplo trans diag N A offA lda X offX incX :=
    dtrsv order uplo trans diag N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbsv order uplo trans diag N K A offA lda X offX incX :=
    dtbsv order uplo trans diag N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpsv order uplo trans diag N A offA X offX incX :=
    dtpsv order uplo trans diag N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  ger order M N a X offX incX Y offY incY A offA lda :=
    dger order M.toUSize N.toUSize a X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize

  her order uplo N alpha X offX incX A offA lda :=
    dsyr order uplo N.toUSize alpha X offX.toUSize incX.toUSize A offA.toUSize lda.toUSize

  her2 order uplo N alpha X offX incX Y offY incY A offA lda :=
    dsyr2 order uplo N.toUSize alpha X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize
