import LeanBLAS.Scalar

namespace BLAS


structure DenseVector.Storage where
  /-- Starting offset -/
  offset : Nat
  /-- Element increment -/
  inc : Nat

namespace DenseVector.Storage

variable {R K Array : Type} [Scalar R K]

def IsValid (strg : Storage) (dataSize : Nat) (n : Nat) : Prop :=
  1 ≤ strg.inc
  ∧
  strg.inc * n + strg.offset ≤ dataSize

instance (strg : Storage) (dataSize n : Nat) : Decidable (IsValid strg dataSize n) := by
  unfold IsValid; infer_instance

def linIdx (strg : Storage) (i : Fin n) : Nat :=
  strg.offset + i.1 * strg.inc


def IsValidLinearIndex (strg : Storage) (dataSize n : Nat) (idx : Nat) : Prop :=
  strg.offset ≤ idx
  ∧
  idx < dataSize
  ∧
  (idx - strg.offset) % strg.inc = 0
  ∧
  (idx - strg.offset) / strg.inc < n

instance (strg : Storage) : Decidable (IsValidLinearIndex strg dataSize n idx) := by
  unfold IsValidLinearIndex; infer_instance

def toI (strg : Storage) (dataSize n : Nat) (idx : Nat)
    (h : strg.IsValidLinearIndex dataSize n idx) : Fin n :=
  ⟨(idx - strg.offset) / strg.inc, by simp_all[IsValidLinearIndex,h]⟩

theorem isValidLinearIndex_linIdx {strg : Storage} {n : Nat} {i : Fin n}
    (hstrg : strg.IsValid dataSize n) :
    strg.IsValidLinearIndex dataSize n (strg.linIdx i) := by
  have := i.2
  simp_all [IsValidLinearIndex, IsValid]
  sorry

@[simp]
theorem linIdx_toI (strg : Storage) (dataSize n : Nat) (idx : Nat)
    (h : strg.IsValidLinearIndex dataSize n idx) :
    linIdx strg (strg.toI dataSize n idx h) = idx := by
  simp [toI, linIdx, IsValidLinearIndex] at h
  simp [linIdx, toI, h.2]
  sorry

@[simp]
theorem toI_linIdx (strg : Storage) (i : Fin n) (hstrg : strg.IsValid dataSize n) :
    strg.toI dataSize n (strg.linIdx i) (isValidLinearIndex_linIdx hstrg) = i := by
  simp [toI, linIdx, isValidLinearIndex_linIdx]
  sorry

def IsPacked (strg : Storage) (dataSize n : Nat) : Prop :=
  strg.inc = 1
  ∧
  strg.offset = 0
  ∧
  dataSize = n

instance (strg : Storage) (dataSize : Nat) : Decidable (IsPacked strg dataSize n) := by
  unfold IsPacked; infer_instance

end DenseVector.Storage
