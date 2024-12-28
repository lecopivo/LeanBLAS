import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.Vector.DenseVector
import LeanBLAS.Util

namespace BLAS

open LevelOneData LevelTwoData

/-- Storage for dense matrix storage. -/
structure DenseMatrix.Storage where
  /-- Row or column major order -/
  order : Order
  /-- Leading dimension size -/
  lda : Nat
  /-- Starting offset -/
  offset : Nat

namespace DenseMatrix.Storage

/-- Is the storage valid for the given data and dimensions? -/
def IsValid (strg : Storage) (dataSize m n : Nat) : Prop :=
  match strg.order with
  | .RowMajor =>
    n ≤ strg.lda
    ∧
    (m * strg.lda) + strg.offset ≤ dataSize
  | .ColMajor =>
    m ≤ strg.lda
    ∧
    (strg.lda * n) + strg.offset ≤ dataSize

instance (strg : Storage) (dataSize m n : Nat) : Decidable (IsValid strg dataSize m n) :=
  by
    unfold IsValid
    exact
     match h : strg.order with
     | .RowMajor => inferInstance
     | .ColMajor => inferInstance


/-- Linear index of matrix element `(i, j)` in a matrix of size `m` by `n`. -/
def linIdx (strg : Storage) (i : Fin m) (j : Fin n) : Nat :=
  match strg.order with
  | .RowMajor => j.1 + strg.lda * i.1 + strg.offset
  | .ColMajor => i.1 + strg.lda * j.1 + strg.offset


/-- Can `idx` be used to index m×n matrix's data buffer of size `dataSize`?  -/
def IsValidLinearIndex (strg : Storage) (dataSize m n : Nat) (idx : Nat) : Prop :=
  strg.offset ≤ idx
  ∧
  idx < dataSize
  ∧
  match strg.order with
  | .RowMajor =>
    let i := (idx - strg.offset) / strg.lda
    let j := (idx - strg.offset) % strg.lda
    i < m ∧ j < n
  | .ColMajor =>
    let i := (idx - strg.offset) % strg.lda
    let j := (idx - strg.offset) / strg.lda
    i < m ∧ j < n


instance (strg : Storage) (dataSize m n idx : Nat) : Decidable (IsValidLinearIndex strg dataSize m n idx) :=
  by
    unfold IsValidLinearIndex
    exact
     match h : strg.order with
     | .RowMajor => inferInstance
     | .ColMajor => inferInstance


/-- Convert linear index to matrix indices. -/
def toIJ (strg : Storage) (dataSize m n : Nat) (idx : Nat)
    (h : strg.IsValidLinearIndex dataSize m n idx) : Fin m × Fin n :=
  match h' : strg.order with
  | .RowMajor =>
    let i := (idx - strg.offset) / strg.lda
    let j := (idx - strg.offset) % strg.lda
    (⟨i, by simp_all[IsValidLinearIndex,h,h']⟩, ⟨j, by simp_all[IsValidLinearIndex,h,h']⟩)
  | .ColMajor =>
    let i := (idx - strg.offset) % strg.lda
    let j := (idx - strg.offset) / strg.lda
    (⟨i, by simp_all[IsValidLinearIndex,h,h']⟩, ⟨j, by simp_all[IsValidLinearIndex,h,h']⟩)

theorem isValidLinearIndex_linIdx {strg : Storage} {dataSize m n : Nat} {i : Fin m} {j : Fin n}
    (hstrg : strg.IsValid dataSize m n) :
    strg.IsValidLinearIndex dataSize m n (strg.linIdx i j) := by
  rcases strg with ⟨order,lda,offset⟩
  simp_all only [linIdx, IsValidLinearIndex,IsValid]
  cases order
  · simp_all only [Nat.le_add_left, Nat.add_sub_cancel, Nat.add_mul_mod_self_left, true_and];
    sorry
  · simp_all only [Nat.le_add_left, Nat.add_sub_cancel, Nat.add_mul_mod_self_left, true_and];
    sorry

@[simp]
theorem linIdx_toIJ (strg : Storage) (dataSize m n : Nat) (idx : Nat)
    (h : strg.IsValidLinearIndex dataSize m n idx) :
    linIdx strg (toIJ strg dataSize m n idx h).1 (toIJ strg dataSize m n idx h).2 = idx := by
  rcases strg with ⟨order,lda,offset⟩
  simp only [linIdx, toIJ]
  cases order <;> simp only [Nat.mod_add_div, Nat.sub_add_cancel h.1]


@[simp]
theorem toIJ_linIdx (strg : Storage) (dataSize m n : Nat) (i : Fin m) (j : Fin n)
    (hstrg : strg.IsValid dataSize m n) :
    toIJ strg dataSize m n (linIdx strg i j) (isValidLinearIndex_linIdx hstrg) = (i,j) := by
  rcases strg with ⟨order,lda,offset⟩
  rcases i with ⟨i,hi⟩
  rcases j with ⟨j,hj⟩
  have hlda : 0 < lda := sorry -- I think we need to fix definition of `IsValid`
  simp only [linIdx, toIJ]
  cases order
  · simp
    have hj' : j < lda := by have := hstrg.1; simp_all only [gt_iff_lt]; omega
    constructor
    · simp_all only [Nat.add_mul_div_left, Nat.div_eq_of_lt, Nat.zero_add]
    · apply Nat.mod_eq_of_lt hj'
  · simp
    have hi' : i < lda := by have := hstrg.1; simp_all only [gt_iff_lt]; omega
    constructor
    · apply Nat.mod_eq_of_lt hi'
    · simp_all only [Nat.add_mul_div_left, Nat.div_eq_of_lt, Nat.zero_add]


/-- Is the data packed according to the storage? i.e. `data` stores m by n` matrix in
a contiguous block of memory.  -/
def IsPacked
    (strg : Storage) (dataSize m n : Nat) : Prop :=
  match strg.order with
  | .RowMajor =>
    n = strg.lda
    ∧
    strg.offset = 0
    ∧
    (m * n) = dataSize
  | .ColMajor =>
    m = strg.lda
    ∧
    strg.offset = 0
    ∧
    (m * n) = dataSize

instance (strg : Storage) (dataSize m n : Nat) : Decidable (IsPacked strg dataSize m n) :=
  by
    unfold IsPacked
    exact
     match h : strg.order with
     | .RowMajor => inferInstance
     | .ColMajor => inferInstance

end DenseMatrix.Storage


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
  [LevelOne R K Array] [LevelOneDataExt R K Array] [LevelTwoData R K Array]


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



omit [LevelTwoData R K Array] [LevelOneDataExt R K Array] in
theorem inbounds (A : K^[m,n]) :
    ∀ (i : Fin (size A.data)), InBounds A.data 0 1 i := by
  intro i; constructor <;> simp

theorem inbounds' (A : K^[m,n]) (i : Fin m) (j : Fin n) : mstrg.linIdx i j < size A.data := sorry

theorem missing_theorem (n m i : Nat) (h : i < m) : n + n * i ≤ n * m := by
  sorry -- nlinarith

theorem inbounds_row (A : K^[m,n]) (h : mstrg.order = .RowMajor) (i : Fin m) (j : Fin n) :
    j.1 + mstrg.lda * i.1 + mstrg.offset < size A.data := by
  rcases mstrg with ⟨order,lda,offset⟩
  have h' := A.valid_storage
  simp_all only [Storage.IsValid, h]
  have := h'.1
  have := h'.2
  calc _ <  n + lda * i + offset := by have := j.2; omega
       _ ≤  lda + lda * i + offset := by omega
       _ ≤  lda + lda * (m - 1) + offset := by have := i.2; sorry -- nlinarith
       _ =  lda * m + offset := by sorry -- ring
       _ ≤  size A.data := by rw[Nat.mul_comm]; exact h'.2

theorem inbounds_col (A : K^[m,n]) (h : mstrg.order = .ColMajor) (i : Fin m) (j : Fin n) :
    i.1 + mstrg.lda * j.1 + mstrg.offset < size A.data := by
  rcases mstrg with ⟨order,lda,offset⟩
  have h' := A.valid_storage
  simp_all only [Storage.IsValid, h]
  have := h'.1
  have := h'.2
  calc _ <  m + lda * j + offset := by have := j.2; omega
       _ ≤  lda + lda * j + offset := by omega
       _ ≤  lda + lda * (n - 1) + offset := by have := i.2; sorry  -- nlinarith
       _ =  lda * n + offset := by sorry  -- ring
       _ ≤  size A.data := by exact h'.2




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

def dot (A B : K^[n,m]) : K :=
  liftRed₂ A B (LevelOneData.dot) (·+·) 0

def nrm2 (A : K^[n,m]) : R :=
  liftRed A (LevelOneData.nrm2) (fun val vali => val + vali*vali) 0
    (finalize := Scalar.sqrt)

def asum (A : K^[n,m]) : R :=
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

def axpy (a : K) (A B : K^[n,m]) : K^[n,m] := lift₂ A B (LevelOneData.axpy (α:=a)) (by intros; simp)
def scal (a : K) (A : K^[n,m])   : K^[n,m] := lift A (LevelOneData.scal (α:=a)) (by intros; simp)


/- Level 1 operations extension -/

def const (m n : Nat) (mstrg : Storage) (k : K) : DenseMatrix Array mstrg m n K :=
  ⟨LevelOneDataExt.const (m*mstrg.lda + mstrg.offset) k, sorry⟩

def sum (A : K^[n,m]) : K :=
  LevelOneDataExt.sum (size A.data) A.data mstrg.offset 1

def axpby (a b : K) (X Y : K^[n,m]) : K^[n,m] :=
  lift₂ X Y (LevelOneDataExt.axpby (α:=a) (β:=b)) (by intros; sorry)

def mul (X Y : K^[n,m]) : K^[n,m] :=
  lift₂ X Y (LevelOneDataExt.mul) (by intros; sorry)

def div (X Y : K^[n,m]) : K^[n,m] :=
  lift₂ X Y (LevelOneDataExt.div) (by intros; sorry)

def inv (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.inv) (by intros; sorry)

def abs (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.abs) (by intros; sorry)

def sqrt (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.sqrt) (by intros; sorry)

def exp (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.exp) (by intros; sorry)

def log (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.log) (by intros; sorry)

def sin (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.sin) (by intros; sorry)

def cos (X : K^[n,m]) : K^[n,m] :=
  lift X (LevelOneDataExt.cos) (by intros; sorry)


/- Derived Level 1 operations for matrices -/

def trace (A : K^[n,n]) : K := LevelOneDataExt.sum n A.data mstrg.offset (mstrg.lda+1)

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

def rowAxpby (i : Fin m) (a b : K) (v : K^[n]) (A : K^[m,n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneDataExt.axpby n a b v.data vstrg.offset vstrg.inc A.data (mstrg.offset + mstrg.lda * i.1) 1,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneDataExt.axpby n a b v.data vstrg.offset vstrg.inc A.data (mstrg.offset + i.1) mstrg.lda,
     by sorry⟩

def col (A : K^[m,n]) (i : Fin m) : K^[n] :=
  let vdata : Array := LevelOneDataExt.const (vstrg.offset + vstrg.inc*n) 0
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + i.1) mstrg.lda vdata vstrg.offset vstrg.inc,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n A.data (mstrg.offset + mstrg.lda * i.1) 1 vdata vstrg.offset vstrg.inc,
     by sorry⟩

def colSet (A : K^[m,n]) (i : Fin m) (v : K^[n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + i.1) mstrg.lda,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneData.copy n v.data vstrg.offset vstrg.inc A.data (mstrg.offset + mstrg.lda * i.1) 1,
     by sorry⟩

def colAxpby (i : Fin m) (a b : K) (v : K^[n]) (A : K^[m,n]) : K^[m,n] :=
  match mstrg.order with
  | .RowMajor =>
    ⟨LevelOneDataExt.axpby n a b v.data vstrg.offset vstrg.inc A.data (mstrg.offset + i.1) 1,
     by sorry⟩
  | .ColMajor =>
    ⟨LevelOneDataExt.axpby n a b v.data vstrg.offset vstrg.inc A.data (mstrg.offset + mstrg.lda * i.1) mstrg.lda,
     by sorry⟩


def diag (v : K^[n]) : K^[n,n] :=
  let A : K^[n,n] := const n n mstrg 0
  ⟨LevelOneData.copy n v.data  vstrg.offset vstrg.inc A.data mstrg.offset (mstrg.lda+1),
   by sorry⟩


def diagonal (A : K^[n,n]) : K^[n] :=
  let vdata : Array := LevelOneDataExt.const n 0
  ⟨LevelOneData.copy n A.data mstrg.offset (mstrg.lda+1) vdata vstrg.offset vstrg.inc,
   by sorry⟩


end DenseMatrix
