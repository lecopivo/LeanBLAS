import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.CBLAS.LevelTwo
import LeanBLAS.Vector.DenseVector
import LeanBLAS.Matrix.DenseMatrix

namespace BLAS

open LevelOneData LevelTwoData BLAS.Sorry

/-- Triangular matrix storing data in packed format i.e. array with `(n*(n+1))/2` elements.  -/
structure TriangularMatrix (Array : Type _) (order : Order) (uplo : UpLo) (n : Nat)
    {R : Type} (K : Type) [Scalar R K] [LevelOneData Array R K]
  where
  data : DenseVector Array .normal ((n*(n+1))/2) K

 -- TriangularMatrix (Array : Type) (order : Order) (uplo : UpLo) (n : Nat)
 --    {R : Type} (K : Type) [Scalar R K] [LevelOneData R K Array]
 --  where
 --  data : DenseVector Array .normal ((n*(n+1))/2) K


namespace TriangularMatrix

variable
  {Array : Type}  {m n : Nat} {ord : Order} {uplo : UpLo}
  {R K : Type} [Scalar R R] [Scalar R K]
  {vstrg : DenseVector.Storage}
  [LevelOne Array R K]

/-- Triangular `n×n` matrix -/
local notation "𝒯[" K ";" n "]" => TriangularMatrix Array ord uplo n K
local notation K "^[" n "]" => DenseVector Array vstrg n K

def IsValidIJ (uplo : UpLo) (i j : Fin n) : Prop :=
  match uplo with
  | .Upper => i <= j
  | .Lower => j <= i

instance {n} (uplo) (i j : Fin n) : Decidable (IsValidIJ uplo i j) :=
  match uplo with
  | .Upper => by dsimp[IsValidIJ]; infer_instance
  | .Lower => by dsimp[IsValidIJ]; infer_instance


-- Did I get this right?
def toLinIdx {n} (ord : Order) (uplo : UpLo) (i j : Fin n) (h : IsValidIJ uplo i j) :
    Fin ((n*(n+1))/2) :=
  match ord, uplo with
  | .ColMajor, .Lower =>
    ⟨i.1 - j.1 + (n*(n+1)-((n-j.1)*(n-j.1+1)))/2, sorry_proof⟩
  | .RowMajor, .Upper =>
    ⟨j.1 - i.1 + (n*(n+1)-((n-i.1)*(n-i.1+1)))/2, sorry_proof⟩
  | .ColMajor, .Upper =>
    ⟨i.1 + (j.1*(j.1+1))/2, sorry_proof⟩
  | .RowMajor, .Lower =>
    ⟨j.1 + (i.1*(i.1+1))/2, sorry_proof⟩

set_option linter.unusedVariables false in
def toIJ {n} (ord : Order) (uplo : UpLo) (idx : Fin ((n*(n+1))/2)) : Fin n × Fin n :=
  have : Inhabited (Fin n) := ⟨⟨0, sorry_proof⟩⟩
  panic! "toIJ not implemented"
  -- match ord, uplo with
  -- | .ColMajor, .Lower => sorry
  -- | .RowMajor, .Upper => sorry
  -- | .ColMajor, .Upper =>
  --   let j : Fin n := ⟨(-1.0 + Float.sqrt (1 + 8.0 * idx.1.toFloat)) / 2.0 |>.toUInt64 |>.toNat,
  --                     sorry_proof /- good luck prooving this :) -/⟩
  --   let i := ⟨idx.1 - (j.1*(j.1+1))/2, sorry_proof⟩
  --   (i,j)
  -- | .RowMajor, .Lower =>
  --   let i : Fin n := ⟨(-1.0 + Float.sqrt (1 + 8.0 * idx.1.toFloat)) / 2.0 |>.toUInt64 |>.toNat,
  --                     sorry_proof /- good luck prooving this :) -/⟩
  --   let j := ⟨idx.1 - (i.1*(i.1+1))/2, sorry_proof⟩
  --   (i,j)

-- It would be really nice to have proofs of this!
@[simp]
theorem isValidIJ_toIJ {n} (ord : Order) (uplo : UpLo) (idx : Fin ((n*(n+1))/2)) :
  IsValidIJ uplo (toIJ ord uplo idx).1 (toIJ ord uplo idx).2 := sorry_proof

-- It would be really nice to have proofs of this!
@[simp]
theorem toLinIdx_toIJ {n} (ord : Order) (uplo : UpLo) (idx : Fin ((n*(n+1))/2)) :
  toLinIdx ord uplo (toIJ ord uplo idx).1 (toIJ ord uplo idx).2 (by simp)
  =
  idx := sorry_proof

@[simp]
theorem toIJ_toLinIdx {n} (ord : Order) (uplo : UpLo) (i j : Fin n) (h : IsValidIJ uplo i j) :
  toIJ ord uplo (toLinIdx ord uplo i j h)
  =
  (i,j) := sorry_proof

def get' (T : 𝒯[K;n]) (i j : Fin n) (h : IsValidIJ uplo i j) : K :=
  T.data.get (toLinIdx ord uplo i j h)

def get (T : 𝒯[K;n]) (i j : Fin n) : K :=
  if h : IsValidIJ uplo i j then
    T.data.get (toLinIdx ord uplo i j h)
  else
    0

def set' (T : 𝒯[K;n]) (i j : Fin n) (v : K) (h : IsValidIJ uplo i j) : 𝒯[K;n] :=
  ⟨T.data.set (toLinIdx ord uplo i j h) v⟩

def set (T : 𝒯[K;n]) (i j : Fin n) (v : K) : 𝒯[K;n] :=
  if h : IsValidIJ uplo i j then
    ⟨T.data.set (toLinIdx ord uplo i j h) v⟩
  else
    T

def toString [ToString K] (T : 𝒯[K;n]) : String := Id.run do
  let mut s : String := "["

  for i in [0:n] do
    let i : Fin n := ⟨i, sorry_proof⟩
    for j in [0:n] do
      let j : Fin n := ⟨j, sorry_proof⟩
      s := s ++ ToString.toString (T.get i j)
      if j +1 < n then
        s := s ++ ", "
    if i + 1< n then
      s := s ++ ";\n"
  return s ++ "]"

instance {n} [ToString K] : ToString (𝒯[K;n]) := ⟨toString⟩

/-  Level 1 operations -/

def dot (A B : 𝒯[K;n]) : K := A.data.dot B.data
def nrm2 (A : 𝒯[K;n]) : R := A.data.nrm2
def asum (A : 𝒯[K;n]) : R := A.data.asum
def iamax [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : 𝒯[K;n]) : Fin n × Fin n :=
  let idx : Fin ((n*(n+1))/2) := A.data.iamax
  toIJ ord uplo idx

def axpy (a : K) (A B : 𝒯[K;n]) : 𝒯[K;n] :=
  ⟨DenseVector.axpy a A.data B.data⟩

def scal (a : K) (A : 𝒯[K;n]) : 𝒯[K;n] :=
  ⟨A.data.scal a⟩

-- def row (T : 𝒯[K;n]) (i : Fin n) : K^[n] := sorry
-- def col (T : 𝒯[K;n]) (i : Fin n) : K^[n] := sorry
-- def diag (v : K^[n]) : 𝒯[K;n] := sorry
-- def diagonal (T : 𝒯[K;n]) : K^[n] := sorry

/- Level 1 extensions -/
variable [LevelOneDataExt Array R K]

def zero : 𝒯[K;n] := ⟨DenseVector.const _ _ 0⟩
def mul (A B : 𝒯[K;n]) : 𝒯[K;n] := ⟨A.data.mul B.data⟩
def imaxRe (A : 𝒯[K;n]) (_h : n ≠ 0) : Fin n × Fin n :=
  let idx := A.data.imaxRe sorry_proof
  toIJ ord uplo idx

def iminRe (A : 𝒯[K;n]) (_h : n ≠ 0) : Fin n × Fin n :=
  let idx := A.data.iminRe sorry_proof
  toIJ ord uplo idx


/- Level 2 operations -/

variable [LevelTwoData Array R K]

def tpmv (T : 𝒯[K;n]) (trans : Transpose) (x : K^[n]) : K^[n] :=
  ⟨LevelTwoData.tpmv ord uplo trans false n T.data.data 0 x.data vstrg.offset vstrg.inc, sorry_proof⟩

/-  Conversion to/from dense -/
variable [LevelOneDataExt Array R K] [LevelTwoDataExt Array R K]

variable  {mstrg : DenseMatrix.Storage} {mord : Order}

local notation K "^[" m "," n "]" => DenseMatrix Array mord mstrg m n K

/-- Converts tringular matrix to dense matrix -/
def toDense (T : 𝒯[K;n]) : K^[n,n] :=
  let Adata := LevelOneDataExt.const (n*n) 0
  ⟨LevelTwoDataExt.packedToDense n uplo ord T.data.data mord Adata mstrg.offset (mstrg.lda mord n n),
  sorry_proof⟩

/-- Extracts triangular part of dense matrix. -/
def _root_.BLAS.DenseMatrix.toTriangular (A : K^[n,n]) (uplo : UpLo) : 𝒯[K;n] :=
  let Tdata := LevelOneDataExt.const ((n*(n+1))/2) 0
  ⟨LevelTwoDataExt.denseToPacked n uplo mord A.data mstrg.offset (mstrg.lda mord n n) ord Tdata,
  sorry_proof⟩
