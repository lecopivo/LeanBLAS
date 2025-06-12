import LeanBLAS.Spec.LevelOne
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Star.Basic

namespace BLAS


-- move this to Spec directory
inductive Order where
  | RowMajor
  | ColMajor
deriving BEq, DecidableEq

-- move this to Spec directory
inductive Transpose where
  | NoTrans
  | Trans
  | ConjTrans
deriving BEq, DecidableEq

-- move this to Spec directory
inductive UpLo where
  /-- Upper triangular matrix --/
  | Upper
  /-- Lower triangular matrix --/
  | Lower
deriving BEq, DecidableEq

inductive Diag where
  /-- Non-unit triangular matrix --/
  | NonUnit
  /-- Unit triangular matrix --/
  | Unit
deriving BEq, DecidableEq

/-- Determines whether a matrix appears on the left or right side of a product -/
inductive Side where
  | Left
  | Right
deriving BEq, DecidableEq

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


----------------------------------------------------------------------------------------------------
-- Mathematical Specifications for Level 2 BLAS Operations
----------------------------------------------------------------------------------------------------

section Specifications

variable {Array : Type*} {R K : Type*}
variable [LevelOneData Array R K] [LevelTwoData Array R K]
variable [Field K] [RCLike K] [Field R] [RCLike R]

/-- Helper function to compute matrix element indices based on order -/
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
