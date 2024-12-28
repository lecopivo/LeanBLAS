import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne


namespace BLAS

open LevelOneData LevelTwoData


structure DenseVector.Storage where
  /-- Starting offset -/
  offset : Nat
  /-- Element increment -/
  inc : Nat

namespace DenseVector.Storage

variable {R K Array : Type} [Scalar R K] [LevelOneData R K Array]

def IsValid (strg : Storage) (data : Array) (n : Nat) : Prop :=
  1 ≤ strg.inc
  ∧
  strg.inc * n + strg.offset ≤ size data

def IsPacked (strg : Storage) (data : Array) (n : Nat) : Prop :=
  strg.inc = 1
  ∧
  strg.offset = 0
  ∧
  size data = n


end DenseVector.Storage

structure DenseVector (Array : Type) (strg : DenseVector.Storage) (n : Nat)
      {R : Type} (K : Type) [Scalar R K] [LevelOneData R K Array]
    where
  data : Array
  is_valid : strg.IsValid data n
