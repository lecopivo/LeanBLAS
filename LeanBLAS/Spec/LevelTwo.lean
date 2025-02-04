import LeanBLAS.Spec.LevelOne

namespace BLAS

-- move this to Spec directory
inductive Order where
  | RowMajor
  | ColMajor

-- move this to Spec directory
inductive Transpose where
  | NoTrans
  | Trans
  | ConjTrans

-- move this to Spec directory
inductive UpLo where
  /-- Upper triangular matrix --/
  | Upper
  /-- Lower triangular matrix --/
  | Lower

inductive Diag where
  /-- Non-unit triangular matrix --/
  | NonUnit
  /-- Unit triangular matrix --/
  | Unit


class LevelTwoData (R K : outParam Type) (Array : Type) [Scalar R K] where

  /-- General matrix-vector multiplication
  ```
  Y := alpha * A * X + beta * Y
  ```
  --/
  gemv (order : Order) (transA : Transpose) (M : Nat) (N : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) (beta : K)
    (Y : Array) (offY incY : Nat) : Array

  bmv (order : Order) (transA : Transpose) (M : Nat) (N : Nat) (KL KU : Nat) (alpha : K)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) (beta : K)
    (Y : Array) (offY incY : Nat) : Array

  trmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  tbmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  tpmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat)
    (X : Array) (offX incX : Nat) : Array

  trsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  tbsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : Nat)
    (A : Array) (offA : Nat) (lda : Nat)
    (X : Array) (offX incX : Nat) : Array

  tpsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : Nat)
    (A : Array) (offA : Nat)
    (X : Array) (offX incX : Nat) : Array

  ger (order : Order) (M : Nat) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array

  her (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array

  her2 (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) (lda : Nat) : Array


class LevelTwoDataExt (R K : outParam Type) (Array : Type) [Scalar R K] where

  /-- General packed rand-1 update
  ```
    A := alpha * m(x * y^H) + A
  ```
  -/
  gpr (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) : array
