import LeanBLAS.Spec.LevelTwo

namespace BLAS

/-- Level 3 BLAS: Matrix-Matrix Operations -/
class LevelThreeData (Array : Type*) (R K : outParam Type*) where

  /-- General matrix-matrix multiplication
  ```
  C := alpha * A * B + beta * C
  ```
  where A is M×K, B is K×N, and C is M×N
  --/
  gemm (order : Order) (transA : Transpose) (transB : Transpose)
    (M : Nat) (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Symmetric matrix-matrix multiplication
  ```
  C := alpha * A * B + beta * C  (when side = Left)
  C := alpha * B * A + beta * C  (when side = Right)
  ```
  where A is symmetric
  --/
  symm (order : Order) (side : Side) (uplo : UpLo)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Symmetric rank-k update
  ```
  C := alpha * A * A^T + beta * C  (when trans = NoTrans)
  C := alpha * A^T * A + beta * C  (when trans = Trans)
  ```
  where C is symmetric
  --/
  syrk (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Symmetric rank-2k update
  ```
  C := alpha * A * B^T + alpha * B * A^T + beta * C  (when trans = NoTrans)
  C := alpha * A^T * B + alpha * B^T * A + beta * C  (when trans = Trans)
  ```
  where C is symmetric
  --/
  syr2k (order : Order) (uplo : UpLo) (trans : Transpose)
    (N : Nat) (K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Triangular matrix-matrix multiplication
  ```
  B := alpha * A * B  (when side = Left)
  B := alpha * B * A  (when side = Right)
  ```
  where A is triangular
  --/
  trmm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

  /-- Triangular solve with multiple right-hand sides
  ```
  op(A) * X = alpha * B  (when side = Left)
  X * op(A) = alpha * B  (when side = Right)
  ```
  where A is triangular, and X overwrites B
  --/
  trsm (order : Order) (side : Side) (uplo : UpLo)
    (transA : Transpose) (diag : Bool)
    (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

end BLAS
