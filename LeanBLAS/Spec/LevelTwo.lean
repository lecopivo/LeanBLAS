import LeanBLAS.Spec.LevelOne

namespace BLAS

-- move this to Spec directory
inductive Order where
  | RowMajor
  | ColMajor
deriving BEq, DecidableEq

def Order.toUInt8 : Order → UInt8
  | RowMajor => 0
  | ColMajor => 1

-- move this to Spec directory
inductive Transpose where
  | NoTrans
  | Trans
  | ConjTrans
deriving BEq, DecidableEq

def Transpose.toUInt8 : Transpose → UInt8
  | NoTrans => 0
  | Trans => 1
  | ConjTrans => 2

-- move this to Spec directory
inductive UpLo where
  /-- Upper triangular matrix --/
  | Upper
  /-- Lower triangular matrix --/
  | Lower
deriving BEq, DecidableEq

def UpLo.toUInt8 : UpLo → UInt8
  | Upper => 0
  | Lower => 1

inductive Diag where
  /-- Non-unit triangular matrix --/
  | NonUnit
  /-- Unit triangular matrix --/
  | Unit
deriving BEq, DecidableEq

def Diag.toUInt8 : Diag → UInt8
  | NonUnit => 0
  | Unit => 1

class LevelTwoData (Array : Type*) (R K : outParam Type*) where

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


/-- Level 2 BLAS function that seems to be missing from the BLAS standard. -/
class LevelTwoDataExt (Array : Type*) (R K : outParam Type*) where

  /-- Copies packed matrix `X` to dense matrix `A`.
  It will zero out elements that are above/bellow the main diagonal. -/
  packedToDense (N : Nat) (uplo : UpLo)
    (orderAp : Order) (Ap : Array) (orderA : Order) (A : Array) (offA : Nat) (lda : Nat) : Array

  /-- Extract uppler/lower triangular part of A and stores it in packed format. -/
  denseToPacked (N : Nat) (uplo : UpLo)
    (orderA : Order) (A : Array) (offA : Nat) (lda : Nat)
    (orderAp : Order) (Ap : Array) : Array

  /-- General packed rand-1 update
  ```
    A := alpha * m(x * y^H) + A
  ```
  -/
  gpr (order : Order) (uplo : UpLo) (N : Nat) (alpha : K)
    (X : Array) (offX incX : Nat)
    (Y : Array) (offY incY : Nat)
    (A : Array) (offA : Nat) : array


-- todo: add spec!!!
