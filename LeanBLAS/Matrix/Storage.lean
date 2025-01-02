import LeanBLAS.Util
import LeanBLAS.Spec.LevelTwo

namespace BLAS

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
