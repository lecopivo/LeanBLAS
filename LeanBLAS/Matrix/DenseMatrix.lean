import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.CBLAS.LevelTwo
import LeanBLAS.Vector.DenseVector

namespace BLAS

open LevelOneData LevelTwoData BLAS.Sorry

namespace DenseMatrix

inductive Storage
  | normal
  | submatrix (offset lda : Nat)
deriving DecidableEq

def Storage.IsValid (strg : Storage) (order : Order) (dataSize : Nat) (m n : Nat) : Prop :=
  match strg with
  | .normal => dataSize = m * n
  | .submatrix offset lda =>
    match order with
    | .RowMajor => offset + lda * m ≤ dataSize
    | .ColMajor => offset + lda * n ≤ dataSize


def Storage.offset (strg : Storage) : Nat :=
  match strg with
  | .normal => 0
  | .submatrix offset _ => offset

def Storage.lda (strg : Storage) (order : Order) (m n : Nat) : Nat :=
  match strg with
  | .normal =>
    match order with
    | .RowMajor => n
    | .ColMajor => m
  | .submatrix _ lda => lda

end DenseMatrix


/-- Dense matrix with `m` rows and `n` columns.  -/
structure DenseMatrix (Array : Type _) (order : Order) (strg : DenseMatrix.Storage) (m n : Nat)
    {R : Type _} (K : Type _) [Scalar R K] [LevelOneData Array R K]
  where
  data : Array
  valid_storage : strg.IsValid order (size data) m n


namespace DenseMatrix

variable
  {Array : Type _} {R K : Type _} {n m : Nat} {ord : Order} {mstrg : Storage} [Scalar R R] [Scalar R K]
  {vstrg : DenseVector.Storage}
  [LevelOne Array R K]


local notation K "^[" m ", " n "]" => DenseMatrix Array ord mstrg m n K
local notation K "^[" n "]" => DenseVector Array vstrg n K

-- /-- Is `idx` a valid linear index for and element of matrix `A`? -/
-- def IsValidLinearIndex (A : K^[m,n]) (idx : Nat) : Prop :=
--   mstrg.IsValidLinearIndex (size A.data) m n idx

-- instance {A : K^[m,n]} {idx : Nat} : Decidable (A.IsValidLinearIndex idx) := by
--   unfold IsValidLinearIndex; infer_instance

def toLinIdx {m n} (order : Order) (strg : Storage) (i : Fin m) (j : Fin n) : Nat :=
  match order, strg with
  | .RowMajor, .normal => j.1 + n * i.1
  | .ColMajor, .normal => i.1 + m * j.1
  | .RowMajor, .submatrix offset lda => j.1 + lda * i.1 + offset
  | .ColMajor, .submatrix offset lda => i.1 + lda * j.1 + offset

set_option linter.unusedVariables false in
def toIJ (order : Order) (strg : Storage) (idx : Nat) (h : True /- valid index -/) : Fin m × Fin n :=
  match order, strg with
  | .RowMajor, .normal => (⟨idx / n, sorry_proof⟩, ⟨idx % n, sorry_proof⟩)
  | .ColMajor, .normal => (⟨idx % m, sorry_proof⟩, ⟨idx / m, sorry_proof⟩)
  | .RowMajor, .submatrix offset lda => (⟨(idx-offset) / lda, sorry_proof⟩, ⟨(idx-offset) % lda, sorry_proof⟩)
  | .ColMajor, .submatrix offset lda => (⟨(idx-offset) % lda, sorry_proof⟩, ⟨(idx-offset) / lda, sorry_proof⟩)

def minDataSize (order : Order) (strg : Storage) (m n : Nat) : Nat :=
  match order, strg with
  | _, .normal => m * n
  | .RowMajor, .submatrix offset lda => offset + lda * m
  | .ColMajor, .submatrix offset lda => offset + lda * n

-- Can we do faster implementations here?
def ofFn (f : Fin m → Fin n → K) : K^[m,n] :=
  let dataSize := minDataSize ord mstrg m n
  ⟨LevelOneData.ofFn fun (idx : Fin dataSize) =>
     let (i,j) := toIJ ord mstrg idx.1 sorry_proof
     f i j,
   sorry_proof⟩

def get (x : K^[m,n]) (i : Fin m) (j : Fin n) : K :=
  LevelOneData.get x.data (toLinIdx ord mstrg i j)

def set (x : K^[m,n]) (i : Fin m) (j : Fin n) (v : K) : K^[m,n] :=
  ⟨LevelOneData.set x.data (toLinIdx ord mstrg i j) v, sorry_proof⟩

@[simp]
theorem get_ofFn (f : Fin m → Fin n → K) (i : Fin m) (j : Fin n) :
    get (ofFn (Array:=Array) (ord:=ord) (mstrg:=mstrg) f) i j = f i j := by
  exact sorry_proof

@[simp]
theorem ofFn_get (A : DenseMatrix Array ord .normal m n K) :
    (ofFn (fun i j => get A i j)) = A := by
  exact sorry_proof


def toString [ToString K] (x : K^[m,n]) : String := Id.run do
  let mut s : String := "["

  for i in [0:m] do
    let i : Fin m := ⟨i, sorry_proof⟩
    for j in [0:n] do
      let j : Fin n := ⟨j, sorry_proof⟩
      s := s ++ ToString.toString (x.get i j)
      if j +1 < n then
        s := s ++ ", "
    if i + 1< m then
      s := s ++ ";\n"
  return s ++ "]"

instance [ToString K] : ToString (K^[m,n]) := ⟨toString⟩

/-- Lift unary operation on buffers to matrix -/
@[inline]
def lift (A : K^[m,n]) (f : Nat → Array → Nat → Nat → Array)
    (hf : ∀ N data off inc, size (f N data off inc) = size data) : K^[m,n] :=
  match mstrg with
  | .normal =>
    ⟨f (m*n) A.data 0 1, by
     have := A.valid_storage
     simp_all⟩
  | .submatrix offset lda =>
    match ord with
    | .RowMajor =>
      if m≤n then
        ⟨Fin.foldl (init := A.data) m (fun data i =>
          f n data (offset + i.1*lda) 1),
          sorry_proof⟩
      else
        ⟨Fin.foldl (init := A.data) n (fun data j =>
          f m data (offset + j.1) lda),
          sorry_proof⟩
    | .ColMajor =>
      if n≤m then
        ⟨Fin.foldl (init := A.data) n (fun data j =>
          f m data (offset + j.1*lda) 1),
          sorry_proof⟩
      else
        ⟨Fin.foldl (init := A.data) m (fun data i =>
          f n data (offset + i.1) lda),
          sorry_proof⟩

@[inline]
def liftRed (A : K^[m,n]) (f : Nat → Array → Nat → Nat → α) (op : α → α → α) (default : α) (finalize : α → α := id) : α :=
  match mstrg with
  | .normal =>
    f (m*n) A.data 0 1
  | .submatrix offset lda =>
    match ord with
    | .RowMajor =>
      if m≤n then
        finalize <| Fin.reducelD default op (fun (i : Fin m) => f n A.data (offset + i.1*lda) 1)
      else
        finalize <| Fin.reducelD default op (fun (j : Fin n) => f m A.data (offset + j.1) lda)
    | .ColMajor =>
      if n≤m then
        finalize <| Fin.reducelD default op (fun (j : Fin n) => f m A.data (offset + j.1*lda) 1)
      else
        finalize <| Fin.reducelD default op (fun (i : Fin m) => f n A.data (offset + i.1) lda)


/-- Lift binary operation on buffers to matrices -/
@[inline]
def lift₂ (A B : K^[m,n]) (f : Nat → Array → Nat → Nat → Array → Nat → Nat → Array)
    (hf : ∀ N data data' off inc off' inc', size (f N data off inc data' off' inc') = size data') : K^[m,n] :=
  match mstrg with
  | .normal =>
    ⟨f (m*n) A.data 0 1 B.data 0 1, by
     have := A.valid_storage
     have := B.valid_storage
     simp_all⟩
  | .submatrix offset lda =>
    match ord with
    | .RowMajor =>
      ⟨Fin.foldl (init := B.data) m (fun data i =>
        f n A.data (offset + i.1*lda) 1 data (offset + i.1*lda) 1),
        sorry_proof⟩
    | .ColMajor =>
      ⟨Fin.foldl (init := B.data) n (fun data j =>
        f m A.data (mstrg.offset + j.1*lda) 1 data (offset + j.1*lda) 1),
        sorry_proof⟩

@[inline]
def liftRed₂ (A B : K^[m,n]) (f : Nat → Array → Nat → Nat → Array → Nat → Nat → α)
    (op : α → α → α) (default : α) (finalize : α → α := id) : α :=
  match mstrg with
  | .normal =>
    f (m*n) A.data 0 1 B.data 0 1
  | .submatrix offset lda =>
    match ord with
    | .RowMajor =>
      finalize <| Fin.reducelD default op (fun (i : Fin m) =>
        f n A.data (offset + i.1*lda) 1 B.data (offset + i.1*lda) 1)
    | .ColMajor =>
      finalize <| Fin.reducelD default op (fun (j : Fin n) =>
        f m A.data (offset + j.1*lda) 1 B.data (offset + j.1*lda) 1)


/-  Level 1 operations -/

def dot (A B : K^[m,n]) : K :=
  liftRed₂ A B (LevelOneData.dot) (·+·) 0

def nrm2 (A : K^[m,n]) : R :=
  liftRed A (LevelOneData.nrm2) (fun val vali => val + vali*vali) 0
    (finalize := Scalar.sqrt)

def asum (A : K^[m,n]) : R :=
  liftRed A (LevelOneData.asum) (fun val vali => val + vali) 0

def iamax [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : K^[m,n]) : Fin m × Fin n :=
  let (idx,_) :=
    liftRed A (fun N data off inc =>
      let idx := LevelOneData.iamax N data off inc
      (idx, Scalar.abs (LevelOneData.get data idx)))
      (fun (idx,val) (idx',val') =>
         if val < val' then
           (idx',val')
         else
           (idx,val))
      (0, 0)
  toIJ ord mstrg idx sorry_proof

def axpy (a : K) (A B : K^[m,n]) : K^[m,n] := lift₂ A B (LevelOneData.axpy (α:=a)) (by intros; simp)
def scal (a : K) (A : K^[m,n])   : K^[m,n] := lift A (LevelOneData.scal (α:=a)) (by intros; simp)


/- Level 1 operations extension -/

variable [LevelOneDataExt Array R K]

def const (m n : Nat) (mstrg : Storage) (k : K) : DenseMatrix Array ord mstrg m n K :=
  match mstrg with
  | .normal => ⟨LevelOneDataExt.const (m*n) k, sorry_proof⟩
  | .submatrix offset lda =>
    match ord with
    | .RowMajor => ⟨LevelOneDataExt.const (m*lda + offset) k, sorry_proof⟩
    | .ColMajor => ⟨LevelOneDataExt.const (n*lda + offset) k, sorry_proof⟩

def sum (A : K^[m,n]) : K :=
  liftRed A (fun N data off inc => LevelOneDataExt.sum N data off inc)
    (·+·)
    0

def axpby (a : K) (X : K^[m,n]) (b : K) (Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.axpby (a:=a) (b:=b)) (by intros; sorry_proof)

def scalAdd (a : K) (A : K^[m,n]) (b : K) : K^[m,n] := lift A (LevelOneDataExt.scaladd (a:=a) (b:=b)) sorry_proof

set_option linter.unusedVariables false in
def imaxRe [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : K^[m,n]) (h : 0 < m ∧ 0 < n) : Fin m × Fin n :=
  let (idx,_) :=
    liftRed A (fun N data off inc =>
      let idx := LevelOneDataExt.imaxRe N data off inc sorry_proof
      (idx, Scalar.real (LevelOneData.get data idx)))
      (fun (idx,val) (idx',val') =>
         if val < val' then
           (idx',val')
         else
           (idx,val))
      (0, 0)
  toIJ ord mstrg idx sorry_proof

set_option linter.unusedVariables false in
def iminRe [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : K^[m,n]) (h : 0 < m ∧ 0 < n) : Fin m × Fin n :=
  let (idx,_) :=
    liftRed A (fun N data off inc =>
      let idx := LevelOneDataExt.imaxRe N data off inc sorry_proof
      (idx, Scalar.real (LevelOneData.get data idx)))
      (fun (idx,val) (idx',val') =>
         if val' < val then
           (idx',val')
         else
           (idx,val))
      (0, 0)
  toIJ ord mstrg idx sorry_proof

def mul (X Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.mul) (by intros; sorry_proof)

def div (X Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.div) (by intros; sorry_proof)

def inv (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.inv) (by intros; sorry_proof)

def abs (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.abs) (by intros; sorry_proof)

def sqrt (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.sqrt) (by intros; sorry_proof)

def exp (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.exp) (by intros; sorry_proof)

def log (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.log) (by intros; sorry_proof)

def sin (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.sin) (by intros; sorry_proof)

def cos (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.cos) (by intros; sorry_proof)


/- Derived Level 1 operations for matrices -/

def trace (A : K^[n,n]) : K :=
  match mstrg with
  | .normal => LevelOneDataExt.sum n A.data 0 (n+1)
  | .submatrix offset lda => LevelOneDataExt.sum n A.data offset (lda+1)

def rowStorage (order : Order) (strg : Storage) (i : Fin m) (n : Nat) : DenseVector.Storage :=
  match order, strg with
  | .RowMajor, .normal => .subvector (offset := i.1*n) (inc := 1)
  | .ColMajor, .normal => .subvector (offset := i.1) (inc := n)
  | .RowMajor, .submatrix offset lda => .subvector (offset := offset + lda*i.1) (inc := 1)
  | .ColMajor, .submatrix offset lda => .subvector (offset := offset + i.1) (inc := lda)

def colStorage (order : Order) (strg : Storage) (m : Nat) (j : Fin n) : DenseVector.Storage :=
  match order, strg with
  | .RowMajor, .normal => .subvector (offset := j.1) (inc := m)
  | .ColMajor, .normal => .subvector (offset := j.1*m) (inc := 1)
  | .RowMajor, .submatrix offset lda => .subvector (offset := offset + j.1) (inc := lda)
  | .ColMajor, .submatrix offset lda => .subvector (offset := offset + lda*j.1) (inc := 1)

def rowStorage' (order : Order) (strg : Storage) (i : Fin m) (n : Nat) : DenseMatrix.Storage :=
  match order, strg with
  | .RowMajor, .normal => .submatrix (offset := i.1*n) (lda := n)
  | .ColMajor, .normal => .submatrix (offset := i.1) (lda := m)
  | .RowMajor, .submatrix offset lda => .submatrix (offset := offset + lda*i.1) (lda := lda)
  | .ColMajor, .submatrix offset lda => .submatrix (offset := offset + i.1) (lda := lda)

def colStorage' (order : Order) (strg : Storage) (m : Nat) (j : Fin n) : DenseMatrix.Storage :=
  match order, strg with
  | .RowMajor, .normal => .submatrix (offset := j.1) (lda := n)
  | .ColMajor, .normal => .submatrix (offset := j.1*m) (lda := m)
  | .RowMajor, .submatrix offset lda => .submatrix (offset := offset + j.1) (lda := lda)
  | .ColMajor, .submatrix offset lda => .submatrix (offset := offset + lda*j.1) (lda := lda)

def diagStorage (strg : Storage) (n : Nat) : DenseVector.Storage :=
  match strg with
  | .normal => .subvector (offset := 0) (inc := n+1)
  | .submatrix offset lda => .subvector (offset := offset) (inc := lda+1)

-- row as `n` vector
def row (A : K^[m,n]) (i : Fin m) : DenseVector Array (rowStorage ord mstrg i n) n K :=
  ⟨A.data, sorry_proof⟩

-- col as `m` vector
def col (A : K^[m,n]) (j : Fin n) : DenseVector Array (colStorage ord mstrg m j) m K :=
  ⟨A.data, sorry_proof⟩

-- row as `1×n` matrix
def row' (A : K^[m,n]) (i : Fin m) : DenseMatrix Array ord (rowStorage' ord mstrg i n) 1 n K :=
  ⟨A.data, sorry_proof⟩

-- col as `m×1` matrix
def col' (A : K^[m,n]) (j : Fin n) : DenseMatrix Array ord (colStorage' ord mstrg m j) m 1 K :=
  ⟨A.data, sorry_proof⟩

def diag (v : K^[n]) : K^[n,n] :=
  let A : K^[n,n] := const n n mstrg 0
  ⟨LevelOneData.copy n v.data  vstrg.offset vstrg.inc A.data mstrg.offset ((mstrg.lda ord n n)+1),
   sorry_proof⟩

def diagonal (A : K^[n,n]) : K^[n] :=
  let vdata : Array := LevelOneDataExt.const n 0
  ⟨LevelOneData.copy n A.data mstrg.offset ((mstrg.lda ord n n)+1) vdata vstrg.offset vstrg.inc,
   sorry_proof⟩


/-  Level 2 operations -/

variable  [LevelTwoData Array R K]

def gemv (a : K) (A : K^[m,n]) (x : K^[n]) (b : K) (y : K^[m]) : K^[m] :=
  ⟨LevelTwoData.gemv ord .NoTrans m n a
    A.data mstrg.offset (mstrg.lda ord m n)
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry_proof⟩

def gemvT (a : K) (A : K^[m,n]) (x : K^[m]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelTwoData.gemv ord .Trans m n a
    A.data mstrg.offset (mstrg.lda ord m n)
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry_proof⟩

def gemvH (a : K) (A : K^[m,n]) (x : K^[m]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelTwoData.gemv ord .ConjTrans m n a
    A.data mstrg.offset (mstrg.lda ord m n)
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry_proof⟩

def ger (a : K) (x : K^[m]) (y : K^[n]) (A : K^[m,n]) : K^[m,n] :=
  ⟨LevelTwoData.ger ord m n a
    x.data vstrg.offset vstrg.inc
    y.data vstrg.offset vstrg.inc
    A.data mstrg.offset (mstrg.lda ord m n), sorry_proof⟩

end DenseMatrix
