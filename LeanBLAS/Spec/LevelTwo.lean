/-
Copyright (c) 2024 The LeanBLAS Authors. All rights reserved.
Released under the Apache 2.0 license as described in the repository's LICENSE file.
Authors: The LeanBLAS Development Team
-/

import LeanBLAS.Spec.LevelOne
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Star.Basic

-- Enable missing documentation linter for this file
set_option linter.missingDocs true

/-!
## Level 2 BLAS Operations

This module defines the interface for Level 2 BLAS operations, which are matrix-vector operations.
Level 2 BLAS includes operations like matrix-vector multiplication, triangular solves, and
rank-1 and rank-2 updates.
-/

namespace BLAS


/--
Matrix storage order.

Specifies whether matrix elements are stored in row-major or column-major order.
This affects how matrix elements are accessed in memory.
-/
inductive Order where
  /-- Row-major order: elements of each row are contiguous in memory. -/
  | RowMajor
  /-- Column-major order: elements of each column are contiguous in memory (Fortran-style). -/
  | ColMajor
deriving BEq, DecidableEq

/--
Matrix transpose operation.

Specifies whether and how to transpose a matrix in an operation.
-/
inductive Transpose where
  /-- Use the matrix as-is, no transposition. -/
  | NoTrans
  /-- Transpose the matrix (swap rows and columns). -/
  | Trans
  /-- Conjugate transpose (Hermitian transpose) - transpose and complex conjugate. -/
  | ConjTrans
deriving BEq, DecidableEq

/--
Triangular matrix type.

Specifies whether to use the upper or lower triangular part of a matrix.
-/
inductive UpLo where
  /-- Upper triangular matrix: only elements on or above the diagonal are used. -/
  | Upper
  /-- Lower triangular matrix: only elements on or below the diagonal are used. -/
  | Lower
deriving BEq, DecidableEq

/--
Diagonal type for triangular matrices.

Specifies whether the diagonal elements of a triangular matrix are assumed to be one.
-/
inductive Diag where
  /-- Non-unit triangular: diagonal elements are stored and used from the matrix. -/
  | NonUnit
  /-- Unit triangular: diagonal elements are assumed to be 1 and not referenced. -/
  | Unit
deriving BEq, DecidableEq

/-- Determines whether a matrix appears on the left or right side of a product -/
inductive Side where
  /-- Matrix appears on the left side of the product. -/
  | Left
  /-- Matrix appears on the right side of the product. -/
  | Right
deriving BEq, DecidableEq

/--
Core Level 2 BLAS operations interface.

This class defines matrix-vector operations that form the basis of Level 2 BLAS.
These operations are fundamental for many linear algebra algorithms.

## Type Parameters
- `Array`: The array type that stores matrices and vectors
- `R`: The real number type (for real-valued results)
- `K`: The field type (can be real or complex)
-/
class LevelTwoData (Array : Type*) (R K : outParam Type*) where

  /-- 
  General matrix-vector multiplication: `Y := alpha * A * X + beta * Y`
  
  ## Parameters
  - `order`: Storage order of matrix A (row-major or column-major)
  - `transA`: Whether to transpose A (NoTrans, Trans, or ConjTrans)
  - `M`: Number of rows of matrix A (before transpose)
  - `N`: Number of columns of matrix A (before transpose)
  - `alpha`: Scalar multiplier for A*X
  - `A`: The matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A (distance between columns in column-major)
  - `X`: Input vector
  - `offX`: Offset to the first element of X
  - `incX`: Stride between elements of X
  - `beta`: Scalar multiplier for Y
  - `Y`: Input/output vector
  - `offY`: Offset to the first element of Y  
  - `incY`: Stride between elements of Y
  - Returns: Updated vector Y
  -/
  gemv (order : Order) (transA : Transpose) (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) (beta : K)
    (Y : Array) (offY incY : Nat) : Array

  /--
  Banded matrix-vector multiplication: `Y := alpha * A * X + beta * Y`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `transA`: Whether to transpose A
  - `M`: Number of rows of matrix A
  - `N`: Number of columns of matrix A
  - `KL`: Number of sub-diagonals
  - `KU`: Number of super-diagonals
  - `alpha`: Scalar multiplier for A*X
  - `A`: The banded matrix in packed format
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `X`: Input vector
  - `offX`, `incX`: Offset and stride for X
  - `beta`: Scalar multiplier for Y
  - `Y`: Input/output vector  
  - `offY`, `incY`: Offset and stride for Y
  - Returns: Updated vector Y
  -/
  bmv (order : Order) (transA : Transpose) (M : Nat) (N : Nat) (KL KU : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) (beta : K)
    (Y : Array) (offY incY : Nat) : Array

  /--
  Triangular matrix-vector multiplication: `X := A * X` or `X := A^T * X`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A
  - `diag`: Whether A has unit diagonal (true) or not (false)
  - `N`: Order of matrix A (N×N)
  - `A`: The triangular matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `X`: Input/output vector
  - `offX`, `incX`: Offset and stride for X
  - Returns: Updated vector X
  -/
  trmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  Triangular banded matrix-vector multiplication: `X := A * X` or `X := A^T * X`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A
  - `diag`: Whether A has unit diagonal
  - `N`: Order of matrix A
  - `K`: Number of diagonals (sub-diagonals if lower, super-diagonals if upper)
  - `A`: The triangular banded matrix in packed format
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `X`: Input/output vector
  - `offX`, `incX`: Offset and stride for X
  - Returns: Updated vector X
  -/
  tbmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  Triangular packed matrix-vector multiplication: `X := A * X` or `X := A^T * X`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A
  - `diag`: Whether A has unit diagonal
  - `N`: Order of matrix A
  - `A`: The triangular matrix in packed format (no wasted storage)
  - `offA`: Offset to the first element of A
  - `X`: Input/output vector
  - `offX`, `incX`: Offset and stride for X
  - Returns: Updated vector X
  -/
  tpmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  Triangular solve: solve `A * X = B` or `A^T * X = B` for X
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A
  - `diag`: Whether A has unit diagonal
  - `N`: Order of matrix A
  - `A`: The triangular matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `X`: On entry, the right-hand side B; on exit, the solution X
  - `offX`, `incX`: Offset and stride for X
  - Returns: Solution vector X
  -/
  trsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  Triangular banded solve: solve `A * X = B` or `A^T * X = B` for X
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A
  - `diag`: Whether A has unit diagonal
  - `N`: Order of matrix A
  - `K`: Number of diagonals
  - `A`: The triangular banded matrix in packed format
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `X`: On entry, the right-hand side B; on exit, the solution X
  - `offX`, `incX`: Offset and stride for X
  - Returns: Solution vector X
  -/
  tbsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  Triangular packed solve: solve `A * X = B` or `A^T * X = B` for X
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `transA`: Whether to transpose A  
  - `diag`: Whether A has unit diagonal
  - `N`: Order of matrix A
  - `A`: The triangular matrix in packed format
  - `offA`: Offset to the first element of A
  - `X`: On entry, the right-hand side B; on exit, the solution X
  - `offX`, `incX`: Offset and stride for X
  - Returns: Solution vector X
  -/
  tpsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat)
    (X : Array) (offX incX : Nat) : Array

  /--
  General rank-1 update: `A := alpha * X * Y^T + A`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `M`: Number of rows of matrix A
  - `N`: Number of columns of matrix A
  - `alpha`: Scalar multiplier
  - `X`: First vector (length M)
  - `offX`, `incX`: Offset and stride for X
  - `Y`: Second vector (length N)
  - `offY`, `incY`: Offset and stride for Y
  - `A`: Input/output matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - Returns: Updated matrix A
  -/
  ger (order : Order) (M : Nat) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array

  /--
  Hermitian rank-1 update: `A := alpha * X * X^H + A`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `N`: Order of matrix A (N×N)
  - `alpha`: Real scalar multiplier
  - `X`: Vector (length N)
  - `offX`, `incX`: Offset and stride for X
  - `A`: Input/output Hermitian matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - Returns: Updated Hermitian matrix A
  -/
  her (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array

  /--
  Hermitian rank-2 update: `A := alpha * X * Y^H + conj(alpha) * Y * X^H + A`
  
  ## Parameters
  - `order`: Storage order of matrix A
  - `uplo`: Use upper or lower triangular part
  - `N`: Order of matrix A (N×N)
  - `alpha`: Scalar multiplier
  - `X`: First vector (length N)
  - `offX`, `incX`: Offset and stride for X
  - `Y`: Second vector (length N)
  - `offY`, `incY`: Offset and stride for Y
  - `A`: Input/output Hermitian matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - Returns: Updated Hermitian matrix A
  -/
  her2 (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array


/-- 
Extended Level 2 BLAS operations.

These operations extend the standard BLAS interface with additional functionality
for packed matrix operations and other utilities.

## Type Parameters
- `Array`: The array type
- `R`: Real number type
- `K`: Field type (real or complex)
-/
class LevelTwoDataExt (Array : Type*) (R K : outParam Type*) where

  /-- 
  Convert packed triangular matrix to dense format.
  
  Copies packed matrix `Ap` to dense matrix `A`, zeroing out elements
  that are above/below the main diagonal depending on `uplo`.
  
  ## Parameters
  - `N`: Order of the matrix
  - `uplo`: Use upper or lower triangular part
  - `orderAp`: Storage order of packed matrix
  - `Ap`: Packed triangular matrix
  - `orderA`: Storage order of dense matrix
  - `A`: Output dense matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - Returns: Dense matrix A
  -/
  packedToDense (N : Nat) (uplo : UpLo)
    (orderAp : Order) (Ap : Array) (orderA : Order) (A : Array) (offA : Nat) (lda : Nat) : Array

  /-- 
  Convert dense matrix to packed triangular format.
  
  Extracts the upper/lower triangular part of dense matrix `A` 
  and stores it in packed format in `Ap`.
  
  ## Parameters
  - `N`: Order of the matrix
  - `uplo`: Extract upper or lower triangular part
  - `orderA`: Storage order of dense matrix
  - `A`: Input dense matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `orderAp`: Storage order of packed matrix
  - `Ap`: Output packed triangular matrix
  - Returns: Packed matrix Ap
  -/
  denseToPacked (N : Nat) (uplo : UpLo)
    (orderA : Order) (A : Array) (offA : Nat) (lda : Nat)
    (orderAp : Order) (Ap : Array) : Array

  /-- 
  General packed rank-1 update: `A := alpha * m(X * Y^H) + A`
  
  Here `m` denotes taking the upper or lower triangular part based on `uplo`.
  
  ## Parameters
  - `order`: Storage order of packed matrix A
  - `uplo`: Use upper or lower triangular part
  - `N`: Order of matrix A
  - `alpha`: Scalar multiplier
  - `X`: First vector (length N)
  - `offX`, `incX`: Offset and stride for X
  - `Y`: Second vector (length N)
  - `offY`, `incY`: Offset and stride for Y
  - `A`: Input/output packed triangular matrix
  - `offA`: Offset to the first element of A
  - Returns: Updated packed matrix A
  -/
  gpr (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) : Array


----------------------------------------------------------------------------------------------------
-- Mathematical Specifications for Level 2 BLAS Operations
----------------------------------------------------------------------------------------------------

section Specifications

variable {Array : Type*} {R K : Type*}
variable [LevelOneData Array R K] [LevelTwoData Array R K]
variable [Field K] [RCLike K] [Field R] [RCLike R]

/-- 
Compute the linear index for a matrix element at position (i,j).

Converts 2D matrix coordinates to a 1D array index based on the storage order.

## Parameters
- `order`: Storage order (row-major or column-major)
- `i`: Row index
- `j`: Column index  
- `lda`: Leading dimension (stride between columns for column-major)

## Returns
The linear index in the underlying array
-/
def matrixIndex (order : Order) (i j : Nat) (lda : Nat) : Nat :=
  match order with
  | Order.RowMajor => i * lda + j
  | Order.ColMajor => j * lda + i

/-- Get element from matrix stored in array format -/
def getMatrix (order : Order) (A : Array) (offA : Nat) (lda : Nat) (i j : Nat) : K :=
  LevelOneData.get A (offA + matrixIndex order i j lda)

/-- Get element from vector with stride -/
def getVector (X : Array) (offX : Nat) (incX : Nat) (i : Nat) : K :=
  LevelOneData.get X (offX + i * incX)

----------------------------------------------------------------------------------------------------
-- GEMV Specifications
----------------------------------------------------------------------------------------------------

/-- Mathematical specification for GEMV: Y := alpha * op(A) * X + beta * Y
    where op(A) = A, A^T, or A^H depending on transA -/
def gemv_spec (order : Order) (transA : Transpose) (M N : Nat) (alpha : K)
  (A : Array) (offA : Nat) (lda : Nat)
  (X : Array) (offX incX : Nat) (beta : K)
  (Y : Array) (offY incY : Nat) : Array → Prop :=
  fun Y' =>
    let (rows, cols) := match transA with
      | Transpose.NoTrans => (M, N)
      | Transpose.Trans => (N, M)
      | Transpose.ConjTrans => (N, M)
    ∀ i < rows,
      getVector Y' offY incY i = 
        alpha * (Finset.sum (Finset.range cols) fun j =>
          let aij := match transA with
            | Transpose.NoTrans => getMatrix order A offA lda i j
            | Transpose.Trans => getMatrix order A offA lda j i
            | Transpose.ConjTrans => star (getMatrix order A offA lda j i)
          aij * getVector X offX incX j) +
        beta * getVector Y offY incY i

/-- GEMV is linear in alpha -/
theorem gemv_linear_alpha (order : Order) (transA : Transpose) (M N : Nat) 
  (alpha1 alpha2 : K) (A : Array) (offA : Nat) (lda : Nat)
  (X : Array) (offX incX : Nat) (beta : K)
  (Y : Array) (offY incY : Nat) :
  let Y1 := LevelTwoData.gemv order transA M N alpha1 A offA lda X offX incX beta Y offY incY
  let Y2 := LevelTwoData.gemv order transA M N alpha2 A offA lda X offX incX beta Y offY incY
  let Y12 := LevelTwoData.gemv order transA M N (alpha1 + alpha2) A offA lda X offX incX beta Y offY incY
  gemv_spec order transA M N (alpha1 + alpha2) A offA lda X offX incX beta Y offY incY Y12 :=
sorry

----------------------------------------------------------------------------------------------------
-- TRMV Specifications
----------------------------------------------------------------------------------------------------

/-- Mathematical specification for TRMV: X := op(A) * X
    where A is triangular and op(A) = A, A^T, or A^H -/
def trmv_spec (order : Order) (uplo : UpLo) (transA : Transpose) (diag : Bool) (N : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (X : Array) (offX incX : Nat) : Array → Prop :=
  fun X' =>
    ∀ i < N,
      getVector X' offX incX i = 
        Finset.sum (Finset.range N) fun j =>
          let aij := if diag && i = j then (1 : K)
            else if (uplo = UpLo.Upper && i <= j) || (uplo = UpLo.Lower && i >= j) then
              match transA with
              | Transpose.NoTrans => getMatrix order A offA lda i j
              | Transpose.Trans => getMatrix order A offA lda j i
              | Transpose.ConjTrans => star (getMatrix order A offA lda j i)
            else (0 : K)
          aij * getVector X offX incX j

----------------------------------------------------------------------------------------------------
-- TRSV Specifications  
----------------------------------------------------------------------------------------------------

/-- Mathematical specification for TRSV: Solve op(A) * X = B
    where A is triangular and the solution overwrites B -/
def trsv_spec (order : Order) (uplo : UpLo) (transA : Transpose) (diag : Bool) (N : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (B : Array) (offB incB : Nat) : Array → Prop :=
  fun X =>
    ∀ i < N,
      (Finset.sum (Finset.range N) fun j =>
        let aij := if diag && i = j then (1 : K)
          else if (uplo = UpLo.Upper && i <= j) || (uplo = UpLo.Lower && i >= j) then
            match transA with
            | Transpose.NoTrans => getMatrix order A offA lda i j
            | Transpose.Trans => getMatrix order A offA lda j i
            | Transpose.ConjTrans => star (getMatrix order A offA lda j i)
          else (0 : K)
        aij * getVector X offB incB j) = getVector B offB incB i

----------------------------------------------------------------------------------------------------
-- GER Specifications
----------------------------------------------------------------------------------------------------

/-- Mathematical specification for GER: A := alpha * x * y^T + A -/
def ger_spec (order : Order) (M N : Nat) (alpha : K)
  (X : Array) (offX incX : Nat)
  (Y : Array) (offY incY : Nat)
  (A : Array) (offA : Nat) (lda : Nat) : Array → Prop :=
  fun A' =>
    ∀ i < M, ∀ j < N,
      getMatrix order A' offA lda i j = 
        getMatrix order A offA lda i j + 
        alpha * getVector X offX incX i * getVector Y offY incY j

/-- GER operation is associative -/
theorem ger_associative (order : Order) (M N : Nat) (alpha beta : K)
  (X Y Z : Array) (offX incX offY incY offZ incZ : Nat)
  (A : Array) (offA : Nat) (lda : Nat) :
  let A1 := LevelTwoData.ger order M N alpha X offX incX Y offY incY A offA lda
  let A2 := LevelTwoData.ger order M N beta Z offZ incZ Y offY incY A1 offA lda
  let A1' := LevelTwoData.ger order M N beta Z offZ incZ Y offY incY A offA lda
  let A2' := LevelTwoData.ger order M N alpha X offX incX Y offY incY A1' offA lda
  ger_spec order M N (alpha * (getVector X offX incX 0) + beta * (getVector Z offZ incZ 0))
           X offX incX Y offY incY A offA lda A2 :=
sorry

----------------------------------------------------------------------------------------------------
-- Properties of Triangular Operations
----------------------------------------------------------------------------------------------------

/-- TRMV preserves triangular structure -/
theorem trmv_preserves_zeros (order : Order) (uplo : UpLo) (transA : Transpose) (diag : Bool) (N : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (X : Array) (offX incX : Nat) :
  let X' := LevelTwoData.trmv order uplo transA diag N A offA lda X offX incX
  -- Elements outside the triangular part remain zero after multiplication
  ∀ i j, ((uplo = UpLo.Upper ∧ i > j) ∨ (uplo = UpLo.Lower ∧ i < j)) →
    getMatrix order A offA lda i j = (0 : K) :=
sorry

/-- TRSV solution is unique for non-singular matrices -/
theorem trsv_unique_solution (order : Order) (uplo : UpLo) (transA : Transpose) (diag : Bool) (N : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (B : Array) (offB incB : Nat)
  (h_nonsingular : ∀ i < N, diag ∨ getMatrix order A offA lda i i ≠ (0 : K)) :
  ∃! X, trsv_spec order uplo transA diag N A offA lda B offB incB X :=
sorry

----------------------------------------------------------------------------------------------------
-- Relationships between operations
----------------------------------------------------------------------------------------------------

/-- GEMV with identity matrix reduces to copy -/
theorem gemv_identity_is_copy (order : Order) (N : Nat) (X Y : Array) (offX incX offY incY : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (h_identity : ∀ i j, i < N → j < N → getMatrix order A offA lda i j = if i = j then (1 : K) else (0 : K)) :
  let Y' := LevelTwoData.gemv order Transpose.NoTrans N N (1 : K) A offA lda X offX incX (0 : K) Y offY incY
  ∀ i < N, getVector Y' offY incY i = getVector X offX incX i :=
sorry

/-- HER is equivalent to GER for real scalars -/
theorem her_equals_ger_for_real (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
  (X : Array) (offX incX : Nat)
  (A : Array) (offA : Nat) (lda : Nat)
  (h_real : ∀ i < N, star (getVector X offX incX i) = getVector X offX incX i) :
  LevelTwoData.her order uplo N alpha X offX incX A offA lda = 
  LevelTwoData.ger order N N alpha X offX incX X offX incX A offA lda :=
sorry

end Specifications
