import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne

import LeanBLAS.Vector.Storage

import LeanBLAS.Util

namespace BLAS

open LevelOneData LevelTwoData

/-- Dense vector -/
structure DenseVector (Array : Type) (strg : DenseVector.Storage) (n : Nat)
      {R : Type} (K : Type) [Scalar R K] [LevelOneData R K Array]
    where
  data : Array
  valid_storage : strg.IsValid (size data) n


namespace DenseVector

variable {R K Array : Type} [Scalar R R] [Scalar R K] [LevelOne R K Array]
  [LevelOneDataExt R K Array]
  {n m : Nat} {vstrg vstrg' : DenseVector.Storage}

local notation K "^[" n "]" => DenseVector Array vstrg n K
local notation K "^[" n "]'" => DenseVector Array vstrg' n K

def IsPacked (x : K^[n]) : Prop :=
  vstrg.IsPacked (size x.data) n

instance (x : K^[n]) : Decidable (IsPacked x) := by
  unfold IsPacked; infer_instance

def ofFn (f : Fin n → K) : K^[n] :=
  let dataSize := (vstrg.offset + n*vstrg.inc)
  ⟨LevelOneData.ofFn (fun idx : Fin dataSize =>
     let i : Fin n := vstrg.toI dataSize n idx.1 sorry
     f i),
   by sorry⟩

def get (x : K^[n]) (i : Fin n) : K :=
  LevelOneData.get x.data (vstrg.offset + vstrg.inc*i.1)

@[simp]
theorem get_ofFn (f : Fin n → K) (i : Fin n) :
    get (ofFn (Array:=Array) (vstrg:=vstrg) f) i = f i := by
  simp [ofFn, get, LevelOneData.get]
  sorry

@[simp]
theorem ofFn_get (x : K^[n]) (h : x.IsPacked) :
    ofFn (fun i' => get x i') = x := by
  cases h
  simp [ofFn, get, LevelOneData.get]
  sorry


def reinterpret (x : K^[n]) (vstrg' : Storage) (m : Nat) (h : vstrg'.IsValid (size x.data) m) :
    DenseVector Array vstrg' m K :=
  ⟨x.data, h⟩

def toString [ToString K] (x : K^[n]) : String :=
  "[" ++ Fin.reducelD (d:="[]") (fun s si => s ++ ", " ++ si) (fun i : Fin n => ToString.toString (x.get i)) ++ "]"

instance [ToString K] : ToString (K^[n]) := ⟨toString⟩


/-  Level 1 operations -/

def dot (x : K^[n]) (y : K^[n]') : K :=
  LevelOneData.dot n x.data vstrg.offset vstrg.inc y.data vstrg'.offset vstrg'.inc

def nrm2 (x : K^[n]) : R :=
  LevelOneData.nrm2 n x.data vstrg.offset vstrg.inc

def asum (x : K^[n]) : R :=
  LevelOneData.asum n x.data vstrg.offset vstrg.inc

def iamax (x : K^[n]) : Fin n :=
  ⟨LevelOneData.iamax n x.data vstrg.offset vstrg.inc, by sorry⟩

def axpy (α : K) (x y : K^[n]) : K^[n] :=
  ⟨LevelOneData.axpy n α x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, by sorry⟩

def scal (α : K) (x : K^[n]) : K^[n] :=
  ⟨LevelOneData.scal n α x.data vstrg.offset vstrg.inc, by sorry⟩


/- Level 1 operations extension -/

def const (n : Nat) (vstrg : Storage) (k : K) : DenseVector Array vstrg n K :=
  ⟨LevelOneDataExt.const (vstrg.offset + n*vstrg.inc) k, by sorry⟩

def sum (x : K^[n]) : K :=
  LevelOneDataExt.sum n x.data vstrg.offset vstrg.inc

def axpby (a : K) (x : K^[n]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.axpby n a x.data vstrg.offset vstrg.inc b y.data vstrg.offset vstrg.inc, by sorry⟩

def scalAdd (a : K) (x : K^[n]) (b : K) : K^[n] :=
  ⟨LevelOneDataExt.scaladd n a x.data vstrg.offset vstrg.inc b, by sorry⟩

def imaxRe (x : K^[n]) (h : n ≠ 0) : Fin n :=
  ⟨LevelOneDataExt.imaxRe n x.data vstrg.offset vstrg.inc h, sorry⟩

def imaxIm (x : K^[n]) (h : n ≠ 0) : Fin n := ⟨0, by omega⟩

def iminRe (x : K^[n]) (h : n ≠ 0) : Fin n :=
  ⟨LevelOneDataExt.iminRe n x.data vstrg.offset vstrg.inc h, sorry⟩

def iminIm (x : K^[n]) (h : n ≠ 0) : Fin n := ⟨0, by omega⟩

def mul (x y : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.mul n x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, by sorry⟩

def div (x : K^[n]) (y : K^[n]') : K^[n]' :=
  ⟨LevelOneDataExt.div n x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, by sorry⟩

def inv (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.inv n x.data vstrg.offset vstrg.inc, by sorry⟩

def abs (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.abs n x.data vstrg.offset vstrg.inc, by sorry⟩

def sqrt (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.sqrt n x.data vstrg.offset vstrg.inc, by sorry⟩

def exp (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.exp n x.data vstrg.offset vstrg.inc, by sorry⟩

def log (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.log n x.data vstrg.offset vstrg.inc, by sorry⟩

def sin (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.sin n x.data vstrg.offset vstrg.inc, by sorry⟩

def cos (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.cos n x.data vstrg.offset vstrg.inc, by sorry⟩
