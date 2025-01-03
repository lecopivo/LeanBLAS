import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.CBLAS.LevelTwo
import LeanBLAS.Vector.DenseVector
import LeanBLAS.Matrix.Storage

namespace BLAS

open LevelOneData LevelTwoData

/-- Dense matrix with `m` rows and `n` columns.  -/
structure DenseMatrix (Array : Type) (strg : DenseMatrix.Storage) (m n : Nat)
    {R : Type} (K : Type) [Scalar R K] [LevelOneData R K Array]
  where
  data : Array
  valid_storage : strg.IsValid (size data) m n


namespace DenseMatrix

variable
  {Array : Type} {R K : Type} {n m : Nat} {mstrg : Storage} [Scalar R R] [Scalar R K]
  {vstrg : DenseVector.Storage}
  [LevelOne R K Array]


local notation K "^[" m ", " n "]" => DenseMatrix Array mstrg m n K
local notation K "^[" n "]" => DenseVector Array vstrg n K

/-- Is the data packed according to the storage? i.e. `data` stores m by n` matrix in
a contiguous block of memory.  -/
def IsPacked (A : K^[m,n]) : Prop := mstrg.IsPacked (size A.data) m n

/-- Is `idx` a valid linear index for and element of matrix `A`? -/
def IsValidLinearIndex (A : K^[m,n]) (idx : Nat) : Prop :=
  mstrg.IsValidLinearIndex (size A.data) m n idx

instance {A : K^[m,n]} : Decidable (A.IsPacked) := by unfold IsPacked; infer_instance
instance {A : K^[m,n]} {idx : Nat} : Decidable (A.IsValidLinearIndex idx) := by
  unfold IsValidLinearIndex; infer_instance

abbrev toIJ (A : K^[m,n]) (idx : Nat) (h : A.IsValidLinearIndex idx) : Fin m × Fin n :=
  mstrg.toIJ (size A.data) m n idx h

set_option linter.unusedVariables false in
abbrev linIdx (A : K^[m,n]) (i : Fin m) (j : Fin n) : Nat :=
  mstrg.linIdx i j

/-- Matrices `A` and `A'` have identical data that is not directly indexed by indices
`i : Fin m` and `j : Fin n`. -/
def EqualAmbientData (A A' : K^[m,n]) : Prop :=
  ∀ i, ¬(A.IsValidLinearIndex i) → i < size A.data →
       LevelOneData.get A.data i = LevelOneData.get A'.data i


theorem inbounds (A : K^[m,n]) :
    ∀ (i : Fin (size A.data)), InBounds A.data 0 1 i := by
  intro i; constructor <;> simp

theorem inbounds' (A : K^[m,n]) (i : Fin m) (j : Fin n) : mstrg.linIdx i j < size A.data := sorry

theorem missing_theorem (n m i : Nat) (h : i < m) : n + n * i ≤ n * m := by
  sorry -- nlinarith

theorem inbounds_row (A : K^[m,n]) (h : mstrg.order = .RowMajor) (i : Fin m) (j : Fin n) :
    j.1 + mstrg.lda * i.1 + mstrg.offset < size A.data := by
  rcases mstrg with ⟨order,lda,offset,bufferSize⟩
  have h' := A.valid_storage
  simp_all only [Storage.IsValid, h]
  have := h'.1
  have := h'.2
  calc _ <  n + lda * i + offset := by have := j.2; omega
       _ ≤  lda + lda * i + offset := by omega
       _ ≤  lda + lda * (m - 1) + offset := by have := i.2; sorry -- nlinarith
       _ =  lda * m + offset := by sorry -- ring
       _ ≤  size A.data := by rw[Nat.mul_comm]; cases bufferSize <;> simp_all

theorem inbounds_col (A : K^[m,n]) (h : mstrg.order = .ColMajor) (i : Fin m) (j : Fin n) :
    i.1 + mstrg.lda * j.1 + mstrg.offset < size A.data := by
  rcases mstrg with ⟨order,lda,offset,bufferSize⟩
  have h' := A.valid_storage
  simp_all only [Storage.IsValid, h]
  have := h'.1
  have := h'.2
  calc _ <  m + lda * j + offset := by have := j.2; omega
       _ ≤  lda + lda * j + offset := by omega
       _ ≤  lda + lda * (n - 1) + offset := by have := i.2; sorry  -- nlinarith
       _ =  lda * n + offset := by sorry  -- ring
       _ ≤  size A.data := by cases bufferSize <;> simp_all


-- Can we do faster implementations here?
def ofFn (f : Fin m → Fin n → K) : K^[m,n] :=
  let data : Array :=
    match mstrg.order with
    | .RowMajor =>
      LevelOneData.ofFn fun (idx : Fin (m*mstrg.lda + mstrg.offset)) =>
        let (i,j) := mstrg.toIJ (m*mstrg.lda + mstrg.offset) m n idx sorry
        f i j
    | .ColMajor =>
      LevelOneData.ofFn fun (idx : Fin (mstrg.lda*n + mstrg.offset)) =>
        let (i,j) := mstrg.toIJ (m*mstrg.lda + mstrg.offset) m n idx sorry
        f i j
  ⟨data, sorry⟩


def get (x : K^[m,n]) (i : Fin m) (j : Fin n) : K :=
  LevelOneData.get x.data (mstrg.linIdx i j)

@[simp]
theorem get_ofFn (f : Fin m → Fin n → K) (i : Fin m) (j : Fin n) :
    get (ofFn (Array:=Array) (mstrg:=mstrg) f) i j = f i j := by
  simp[ofFn, get]
  cases mstrg.order
  · sorry
  · sorry

@[simp]
theorem ofFn_get (A : K^[m,n]) (hA : A.IsPacked) :
    (ofFn (Array:=Array) (mstrg:=mstrg) (fun i j => get A i j)) = A := by
  rcases mstrg with ⟨order,lda,offset⟩
  simp[get,ofFn]
  sorry


-- /-- Change storage pattern of matrix `A`. This is potentially expensive and it has to move all
-- the data of `A`. -/
-- def changeStorage (A : K^[m,n]) (mstrg' : Storage) (h : mstrg'.IsValid (size A.data) m n) :
--     DenseMatrix Array mstrg' m n K :=
--   sorry
--   -- reshufle data accordingly
--   -- ⟨A.data, h⟩

-- theorem get_changeStorage (A : K^[m,n]) (mstrg' : Storage) (h : mstrg'.IsValid (size A.data) m n)
--     (i : Fin m) (j : Fin n) :
--     get (changeStorage A mstrg' h) i j = get A i j := by
--   sorry

/-- Lift unary operation on buffers to matrix -/
@[inline]
def lift (A : K^[m,n]) (f : Nat → Array → Nat → Nat → Array)
    (hf : ∀ N data off inc, size (f N data off inc) = size data) : K^[m,n] :=
  if A.IsPacked then
    ⟨f (m*n) A.data 0 1, by
     have := A.valid_storage
     simp_all⟩
  else
    match mstrg.order with
    | .RowMajor =>
      ⟨Fin.foldl (init := A.data) m (fun data i =>
        f n data (mstrg.offset + i.1*mstrg.lda) 1),
        sorry⟩
    | .ColMajor =>
      ⟨Fin.foldl (init := A.data) n (fun data j =>
        f m data (mstrg.offset + j.1*mstrg.lda) 1),
        sorry⟩

@[inline]
def liftRed (A : K^[m,n]) (f : Nat → Array → Nat → Nat → α) (op : α → α → α) (default : α) (finalize : α → α := id) : α :=
  if A.IsPacked then
    f (m*n) A.data 0 1
  else
    match mstrg.order with
    | .RowMajor =>
      finalize <| Fin.reducelD default op (fun (i : Fin m) => f n A.data (mstrg.offset + i.1*mstrg.lda) 1)
    | .ColMajor =>
      finalize <| Fin.reducelD default op (fun (j : Fin n) => f m A.data (mstrg.offset + j.1*mstrg.lda) 1)


/-- Lift binary operation on buffers to matrices -/
@[inline]
def lift₂ (A B : K^[m,n]) (f : Nat → Array → Nat → Nat → Array → Nat → Nat → Array)
    (hf : ∀ N data data' off inc off' inc', size (f N data off inc data' off' inc') = size data') : K^[m,n] :=
  if A.IsPacked then
    ⟨f (m*n) A.data 0 1 B.data 0 1, by
     have := A.valid_storage
     have := B.valid_storage
     simp_all⟩
  else
    match mstrg.order with
    | .RowMajor =>
      ⟨Fin.foldl (init := B.data) m (fun data i =>
        f n A.data (mstrg.offset + i.1*mstrg.lda) 1 data (mstrg.offset + i.1*mstrg.lda) 1),
        by
          induction m
          · simp[Fin.foldl,Fin.foldl.loop,B.valid_storage]
          · sorry⟩
    | .ColMajor =>
      ⟨Fin.foldl (init := B.data) n (fun data j =>
        f m A.data (mstrg.offset + j.1*mstrg.lda) 1 data (mstrg.offset + j.1*mstrg.lda) 1),
        by
          induction n
          · simp[Fin.foldl,Fin.foldl.loop,B.valid_storage]
          · sorry⟩

@[inline]
def liftRed₂ (A B : K^[m,n]) (f : Nat → Array → Nat → Nat → Array → Nat → Nat → α)
    (op : α → α → α) (default : α) (finalize : α → α := id) : α :=
  if A.IsPacked then
    f (m*n) A.data 0 1 B.data 0 1
  else
    match mstrg.order with
    | .RowMajor =>
      finalize <| Fin.reducelD default op (fun (i : Fin m) =>
        f n A.data (mstrg.offset + i.1*mstrg.lda) 1 B.data (mstrg.offset + i.1*mstrg.lda) 1)
    | .ColMajor =>
      finalize <| Fin.reducelD default op (fun (j : Fin n) =>
        f m A.data (mstrg.offset + j.1*mstrg.lda) 1 B.data (mstrg.offset + j.1*mstrg.lda) 1)


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
  A.toIJ idx sorry

def axpy (a : K) (A B : K^[m,n]) : K^[m,n] := lift₂ A B (LevelOneData.axpy (α:=a)) (by intros; simp)
def scal (a : K) (A : K^[m,n])   : K^[m,n] := lift A (LevelOneData.scal (α:=a)) (by intros; simp)


/- Level 1 operations extension -/

variable [LevelOneDataExt R K Array]

def const (m n : Nat) (mstrg : Storage) (k : K) : DenseMatrix Array mstrg m n K :=
  match mstrg.order with
  | .RowMajor => ⟨LevelOneDataExt.const (m*mstrg.lda + mstrg.offset) k, sorry⟩
  | .ColMajor => ⟨LevelOneDataExt.const (n*mstrg.lda + mstrg.offset) k, sorry⟩

def sum (A : K^[m,n]) : K :=
  LevelOneDataExt.sum (size A.data) A.data mstrg.offset 1

def axpby (a : K) (X : K^[m,n]) (b : K) (Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.axpby (a:=a) (b:=b)) (by intros; sorry)

def scalAdd (a : K) (A : K^[m,n]) (b : K) : K^[m,n] := lift A (LevelOneDataExt.scaladd (a:=a) (b:=b)) sorry

def imaxRe [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : K^[m,n]) (h : 0 < m ∧ 0 < n) : Fin m × Fin n :=
  let (idx,_) :=
    liftRed A (fun N data off inc =>
      let idx := LevelOneDataExt.imaxRe N data off inc sorry
      (idx, Scalar.real (LevelOneData.get data idx)))
      (fun (idx,val) (idx',val') =>
         if val < val' then
           (idx',val')
         else
           (idx,val))
      (0, 0)
  A.toIJ idx sorry

def iminRe [LT R] [DecidableRel ((·<·) : R → R → Prop)] (A : K^[m,n]) (h : 0 < m ∧ 0 < n) : Fin m × Fin n :=
  let (idx,_) :=
    liftRed A (fun N data off inc =>
      let idx := LevelOneDataExt.imaxRe N data off inc sorry
      (idx, Scalar.real (LevelOneData.get data idx)))
      (fun (idx,val) (idx',val') =>
         if val' < val then
           (idx',val')
         else
           (idx,val))
      (0, 0)
  A.toIJ idx sorry

def mul (X Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.mul) (by intros; sorry)

def div (X Y : K^[m,n]) : K^[m,n] :=
  lift₂ X Y (LevelOneDataExt.div) (by intros; sorry)

def inv (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.inv) (by intros; sorry)

def abs (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.abs) (by intros; sorry)

def sqrt (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.sqrt) (by intros; sorry)

def exp (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.exp) (by intros; sorry)

def log (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.log) (by intros; sorry)

def sin (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.sin) (by intros; sorry)

def cos (X : K^[m,n]) : K^[m,n] :=
  lift X (LevelOneDataExt.cos) (by intros; sorry)


/- Derived Level 1 operations for matrices -/

def trace (A : K^[n,n]) : K := LevelOneDataExt.sum n A.data mstrg.offset (mstrg.lda+1)

def sumRows (A : K^[m,n]) : K^[m] :=
  match mstrg.order with
  | .RowMajor =>
    DenseVector.ofFn fun i => LevelOneDataExt.sum n A.data (mstrg.offset + i.1*mstrg.lda) 1
  | .ColMajor =>
    DenseVector.ofFn fun i => LevelOneDataExt.sum n A.data (mstrg.offset + i.1) (mstrg.lda)

def sumCols (A : K^[m,n]) : K^[n] :=
  match mstrg.order with
  | .RowMajor =>
    DenseVector.ofFn fun j => LevelOneDataExt.sum n A.data (mstrg.offset + j.1) mstrg.lda
  | .ColMajor =>
    DenseVector.ofFn fun j => LevelOneDataExt.sum n A.data (mstrg.offset + j.1*mstrg.lda) 1

def row (A : K^[m,n]) (i : Fin m) : K^[n] :=
  let vdata : Array := LevelOneDataExt.const (vstrg.offset + vstrg.inc*n) 0
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + mstrg.lda * i.1) 1 vdata vstrg.offset vstrg.inc,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + i.1) mstrg.lda vdata vstrg.offset vstrg.inc,
     by sorry⟩

def rowSet (A : K^[m,n]) (i : Fin m) (v : K^[n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + mstrg.lda * i.1) 1,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + i.1) mstrg.lda,
     by sorry⟩

def rowAxpby (i : Fin m) (a : K) (v : K^[n]) (b : K) (A : K^[m,n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneDataExt.axpby n a v.data vstrg.offset vstrg.inc b A.data (mstrg.offset + mstrg.lda * i.1) 1,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneDataExt.axpby n a v.data vstrg.offset vstrg.inc b A.data (mstrg.offset + i.1) mstrg.lda,
     by sorry⟩

def col (A : K^[m,n]) (i : Fin n) : K^[m] :=
  let vdata : Array := LevelOneDataExt.const (vstrg.offset + vstrg.inc*n) 0
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + i.1) mstrg.lda vdata vstrg.offset vstrg.inc,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + mstrg.lda * i.1) 1 vdata vstrg.offset vstrg.inc,
     by sorry⟩

def colSet (A : K^[m,n]) (j : Fin n) (v : K^[m]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + j.1) mstrg.lda,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + mstrg.lda * j.1) 1,
     by sorry⟩

def colAxpby (j : Fin n) (a : K) (v : K^[m]) (b : K) (A : K^[m,n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneDataExt.axpby n a v.data vstrg.offset vstrg.inc b A.data (mstrg.offset + j.1) 1,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneDataExt.axpby n a v.data vstrg.offset vstrg.inc b A.data (mstrg.offset + mstrg.lda * j.1) mstrg.lda,
     by sorry⟩


def diag (v : K^[n]) : K^[n,n] :=
  let A : K^[n,n] := const n n mstrg 0
  ⟨LevelOneData.copy n v.data  vstrg.offset vstrg.inc A.data mstrg.offset (mstrg.lda+1),
   by sorry⟩


def diagonal (A : K^[n,n]) : K^[n] :=
  let vdata : Array := LevelOneDataExt.const n 0
  ⟨LevelOneData.copy n A.data mstrg.offset (mstrg.lda+1) vdata vstrg.offset vstrg.inc,
   by sorry⟩


/-  Level 2 operations -/

variable  [LevelTwoData R K Array]

def gemv (a : K) (A : K^[m,n]) (x : K^[n]) (b : K) (y : K^[m]) : K^[m] :=
  ⟨LevelTwoData.gemv mstrg.order .NoTrans m n 1
    A.data mstrg.offset mstrg.lda
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry⟩

def gemvT (a : K) (A : K^[m,n]) (x : K^[m]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelTwoData.gemv mstrg.order .Trans m n 1
    A.data mstrg.offset mstrg.lda
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry⟩

def gemvH (a : K) (A : K^[m,n]) (x : K^[m]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelTwoData.gemv mstrg.order .ConjTrans m n 1
    A.data mstrg.offset mstrg.lda
    x.data vstrg.offset vstrg.inc b
    y.data vstrg.offset vstrg.inc, sorry⟩

end DenseMatrix
