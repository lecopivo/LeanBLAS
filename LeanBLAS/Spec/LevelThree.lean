import LeanBLAS.Spec.LevelTwo

namespace BLAS

class LevelThreeData (Array : Type*) (R K : outParam Type*) where

  /-- General matrix-matrix multiplication
  ```
  C := alpha * op(A) * op(B) + beta * C
  ```
  --/
  gemm (order : Order) (transA transB : Transpose) (M N K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Symmetric matrix-matrix multiplication
  ```
  C := alpha * A * B + beta * C  (Side.Left)
  C := alpha * B * A + beta * C  (Side.Right)
  ```
  --/
  symm (order : Order) (side : Side) (uplo : UpLo) (M N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Triangular matrix-matrix multiplication
  ```
  B := alpha * op(A) * B  (Side.Left)
  B := alpha * B * op(A)  (Side.Right)
  ```
  --/
  trmm (order : Order) (side : Side) (uplo : UpLo) (transA : Transpose) (diag_enum : Diag) (M N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

  /-- Triangular system solver with multiple right-hand sides
  ```
  op(A) * X = alpha * B  (Side.Left)
  X * op(A) = alpha * B  (Side.Right)
  ```
  --/
  trsm (order : Order) (side : Side) (uplo : UpLo) (transA : Transpose) (diag_enum : Diag) (M N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) : Array

  /-- Symmetric rank-k update
  ```
  C := alpha * A * A^T + beta * C  (trans=NoTrans)
  C := alpha * A^T * A + beta * C  (trans=Trans)
  ```
  --/
  syrk (order : Order) (uplo : UpLo) (trans : Transpose) (N K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

  /-- Symmetric rank-2k update
  ```
  C := alpha * A * B^T + alpha * B * A^T + beta * C  (trans=NoTrans)
  C := alpha * A^T * B + alpha * B^T * A + beta * C  (trans=Trans)
  ```
  --/
  syr2k (order : Order) (uplo : UpLo) (trans : Transpose) (N K_dim : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (B : Array) (offB : Nat) (ldb : Nat) (beta : K)
    (C : Array) (offC : Nat) (ldc : Nat) : Array

export LevelThreeData (gemm symm trmm trsm syrk syr2k)

end BLAS
