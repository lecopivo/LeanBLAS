/-
Copyright (c) 2024 The LeanBLAS Authors. All rights reserved.
Released under the Apache 2.0 license as described in the repository's LICENSE file.
Authors: The LeanBLAS Development Team
-/

import LeanBLAS.Spec.LevelTwo

-- Enable missing documentation linter for this file
set_option linter.missingDocs true

/-!
## Level 3 BLAS Operations

This module defines the interface for Level 3 BLAS operations, which are matrix-matrix operations.
Level 3 BLAS includes the most computationally intensive operations like matrix multiplication,
triangular solves with multiple right-hand sides, and symmetric/Hermitian matrix operations.

These operations achieve the highest performance in BLAS implementations due to their
high arithmetic intensity and opportunities for cache optimization.
-/

namespace BLAS

/-- 
Core Level 3 BLAS operations interface.

This class defines matrix-matrix operations that form the computational core
of many linear algebra algorithms. These operations have O(n³) complexity
and benefit greatly from optimized implementations.

## Type Parameters
- `Array`: The array type that stores matrices
- `R`: The real number type (for real-valued parameters)
- `K`: The field type (can be real or complex)
-/
class LevelThreeData (Array : Type*) (R K : outParam Type*) where

  /-- 
  General matrix-matrix multiplication: `C := alpha * op(A) * op(B) + beta * C`
  
  This is the fundamental operation in linear algebra, used in countless algorithms.
  
  ## Parameters
  - `order`: Storage order of matrices (row-major or column-major)
  - `transA`: Operation on A (NoTrans, Trans, or ConjTrans)
  - `transB`: Operation on B (NoTrans, Trans, or ConjTrans)
  - `M`: Number of rows of op(A) and C
  - `N`: Number of columns of op(B) and C
  - `K_dim`: Number of columns of op(A) and rows of op(B)
  - `alpha`: Scalar multiplier for the product
  - `A`: First input matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `B`: Second input matrix
  - `offB`: Offset to the first element of B
  - `ldb`: Leading dimension of B
  - `beta`: Scalar multiplier for C
  - `C`: Input/output matrix
  - `offC`: Offset to the first element of C
  - `ldc`: Leading dimension of C
  - Returns: Updated matrix C
  
  ## Dimensions
  - If transA = NoTrans: A is M×K_dim, else A is K_dim×M
  - If transB = NoTrans: B is K_dim×N, else B is N×K_dim
  - C is always M×N
  -/
  gemm (order : Order) (transA : Transpose) (transB : Transpose)
    (M : Nat) (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- 
  Symmetric matrix-matrix multiplication.
  
  Computes:
  - `C := alpha * A * B + beta * C` when side = Left
  - `C := alpha * B * A + beta * C` when side = Right
  
  Where A is a symmetric matrix.
  
  ## Parameters
  - `order`: Storage order of matrices
  - `side`: Whether symmetric matrix A is on the left or right
  - `uplo`: Use upper or lower triangular part of A
  - `M`: Number of rows of C
  - `N`: Number of columns of C
  - `alpha`: Scalar multiplier for the product
  - `A`: Symmetric matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `B`: General matrix
  - `offB`: Offset to the first element of B
  - `ldb`: Leading dimension of B
  - `beta`: Scalar multiplier for C
  - `C`: Input/output matrix
  - `offC`: Offset to the first element of C
  - `ldc`: Leading dimension of C
  - Returns: Updated matrix C
  
  ## Dimensions
  - If side = Left: A is M×M, B is M×N
  - If side = Right: A is N×N, B is M×N
  - C is always M×N
  -/
  symm (order : Order) (side : Side) (uplo : UpLo)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- 
  Symmetric rank-k update.
  
  Computes:
  - `C := alpha * A * A^T + beta * C` when trans = NoTrans
  - `C := alpha * A^T * A + beta * C` when trans = Trans
  
  Where C is a symmetric matrix that is updated.
  
  ## Parameters
  - `order`: Storage order of matrices
  - `uplo`: Update upper or lower triangular part of C
  - `trans`: Operation on A (NoTrans or Trans; ConjTrans treated as Trans)
  - `N`: Order of matrix C (N×N)
  - `K_dim`: The other dimension of A
  - `alpha`: Scalar multiplier for the rank-k update
  - `A`: Input matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `beta`: Scalar multiplier for C
  - `C`: Input/output symmetric matrix
  - `offC`: Offset to the first element of C
  - `ldc`: Leading dimension of C
  - Returns: Updated symmetric matrix C
  
  ## Dimensions
  - If trans = NoTrans: A is N×K_dim
  - If trans = Trans: A is K_dim×N
  - C is always N×N (symmetric)
  -/
  syrk (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- 
  Symmetric rank-2k update.
  
  Computes:
  - `C := alpha * A * B^T + alpha * B * A^T + beta * C` when trans = NoTrans
  - `C := alpha * A^T * B + alpha * B^T * A + beta * C` when trans = Trans
  
  Where C is a symmetric matrix that is updated.
  
  ## Parameters
  - `order`: Storage order of matrices
  - `uplo`: Update upper or lower triangular part of C
  - `trans`: Operation on A and B (NoTrans or Trans)
  - `N`: Order of matrix C (N×N)
  - `K_dim`: The other dimension of A and B
  - `alpha`: Scalar multiplier for the rank-2k update
  - `A`: First input matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `B`: Second input matrix
  - `offB`: Offset to the first element of B
  - `ldb`: Leading dimension of B
  - `beta`: Scalar multiplier for C
  - `C`: Input/output symmetric matrix
  - `offC`: Offset to the first element of C
  - `ldc`: Leading dimension of C
  - Returns: Updated symmetric matrix C
  
  ## Dimensions
  - If trans = NoTrans: A and B are N×K_dim
  - If trans = Trans: A and B are K_dim×N
  - C is always N×N (symmetric)
  -/
  syr2k (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- 
  Triangular matrix-matrix multiplication.
  
  Computes:
  - `B := alpha * op(A) * B` when side = Left
  - `B := alpha * B * op(A)` when side = Right
  
  Where A is a triangular matrix and B is overwritten with the result.
  
  ## Parameters
  - `order`: Storage order of matrices
  - `side`: Whether triangular matrix A is on the left or right
  - `uplo`: Use upper or lower triangular part of A
  - `transA`: Operation on A (NoTrans, Trans, or ConjTrans)
  - `diag`: Whether A has unit diagonal (true) or not (false)
  - `M`: Number of rows of B
  - `N`: Number of columns of B
  - `alpha`: Scalar multiplier
  - `A`: Triangular matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `B`: Input/output matrix
  - `offB`: Offset to the first element of B
  - `ldb`: Leading dimension of B
  - Returns: Updated matrix B
  
  ## Dimensions
  - If side = Left: A is M×M
  - If side = Right: A is N×N
  - B is always M×N
  -/
  trmm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

  /-- 
  Triangular solve with multiple right-hand sides.
  
  Solves one of:
  - `op(A) * X = alpha * B` when side = Left
  - `X * op(A) = alpha * B` when side = Right
  
  Where A is triangular, B contains the right-hand sides on entry,
  and is overwritten by the solution X on exit.
  
  ## Parameters
  - `order`: Storage order of matrices
  - `side`: Whether to solve from the left or right
  - `uplo`: Use upper or lower triangular part of A
  - `transA`: Operation on A (NoTrans, Trans, or ConjTrans)
  - `diag`: Whether A has unit diagonal (true) or not (false)
  - `M`: Number of rows of B (and X)
  - `N`: Number of columns of B (and X)
  - `alpha`: Scalar multiplier for right-hand side
  - `A`: Triangular coefficient matrix
  - `offA`: Offset to the first element of A
  - `lda`: Leading dimension of A
  - `B`: On entry, the right-hand sides; on exit, the solution X
  - `offB`: Offset to the first element of B
  - `ldb`: Leading dimension of B
  - Returns: Solution matrix X (overwrites B)
  
  ## Dimensions
  - If side = Left: A is M×M, solving for X in AX=αB
  - If side = Right: A is N×N, solving for X in XA=αB
  - B (and X) is always M×N
  -/
  trsm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

end BLAS
