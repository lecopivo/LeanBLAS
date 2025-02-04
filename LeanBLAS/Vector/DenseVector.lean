import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne

-- import LeanBLAS.Vector.Storage

import LeanBLAS.Util

namespace BLAS

open LevelOneData LevelTwoData BLAS.Sorry

namespace DenseVector

inductive Storage
  | normal
  | subvector (offset inc : Nat)

def Storage.IsValid (strg : Storage) (dataSize : Nat) (n : Nat) : Prop :=
  match strg with
  | .normal => dataSize = n
  | .subvector offset inc => offset + n * inc ≤ dataSize

def Storage.offset (strg : Storage) : Nat :=
  match strg with
  | .normal => 0
  | .subvector offset _ => offset

def Storage.inc (strg : Storage) : Nat :=
  match strg with
  | .normal => 1
  | .subvector _ inc => inc

end DenseVector

/-- Dense vector -/
structure DenseVector (Array : Type) (strg : DenseVector.Storage) (n : Nat)
      {R : Type} (K : Type) [Scalar R K] [LevelOneData R K Array]
    where
  data : Array
  valid_storage : strg.IsValid (size data) n


namespace DenseVector

variable {R K Array : Type} [Scalar R R] [Scalar R K] [LevelOne R K Array]
  [LevelOneDataExt R K Array]
  {n m : Nat} {vstrg vstrg' : Storage}

local notation K "^[" n "]"  => DenseVector Array vstrg n K
local notation K "^[" n "]'" => DenseVector Array vstrg' n K

def ofFn (f : Fin n → K) : K^[n] :=
  match vstrg with
  | .normal => ⟨LevelOneData.ofFn f, sorry_proof⟩
  | .subvector offset inc =>
    let dataSize := offset + n*inc
    ⟨LevelOneData.ofFn (fun idx : Fin dataSize =>
       let i : Fin n := ⟨(idx.1 - offset) / inc, sorry_proof⟩
       f i),
     sorry_proof⟩

def get (x : K^[n]) (i : Fin n) : K :=
  match vstrg with
  | .normal => LevelOneData.get x.data i
  | .subvector offset inc => LevelOneData.get x.data (offset + i.1*inc)

def set (x : K^[n]) (i : Fin n) (v : K) : K^[n] :=
  match vstrg with
  | .normal => ⟨LevelOneData.set x.data i v, sorry_proof⟩
  | .subvector offset inc => ⟨LevelOneData.set x.data (offset + i.1*inc) v, sorry_proof⟩

omit [LevelOneDataExt R K Array] in
@[simp]
theorem get_ofFn (f : Fin n → K) (i : Fin n) :
    get (ofFn (Array:=Array) (vstrg:=vstrg) f) i = f i := by
  simp [ofFn, get, LevelOneData.get]
  exact sorry_proof

omit [LevelOneDataExt R K Array] in
@[simp]
theorem ofFn_get (x : DenseVector Array .normal n K) :
    ofFn (fun i' => get x i') = x := by
  simp [ofFn, get, LevelOneData.get]
  exact sorry_proof

-- def reinterpret (x : K^[n]) (vstrg' : Storage) (m : Nat) (h : vstrg'.IsValid (size x.data) m) :
--     DenseVector Array vstrg' m K :=
--   ⟨x.data, h⟩

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
  ⟨LevelOneData.iamax n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def axpy (α : K) (x y : K^[n]) : K^[n] :=
  ⟨LevelOneData.axpy n α x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, sorry_proof⟩

def scal (α : K) (x : K^[n]) : K^[n] :=
  ⟨LevelOneData.scal n α x.data vstrg.offset vstrg.inc, sorry_proof⟩


/- Level 1 operations extension -/

def const (n : Nat) (vstrg : Storage) (k : K) : DenseVector Array vstrg n K :=
  ⟨LevelOneDataExt.const (vstrg.offset + n*vstrg.inc) k, sorry_proof⟩

def sum (x : K^[n]) : K :=
  LevelOneDataExt.sum n x.data vstrg.offset vstrg.inc

def axpby (a : K) (x : K^[n]) (b : K) (y : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.axpby n a x.data vstrg.offset vstrg.inc b y.data vstrg.offset vstrg.inc, sorry_proof⟩

def scalAdd (a : K) (x : K^[n]) (b : K) : K^[n] :=
  ⟨LevelOneDataExt.scaladd n a x.data vstrg.offset vstrg.inc b, sorry_proof⟩

def imaxRe (x : K^[n]) (h : n ≠ 0) : Fin n :=
  ⟨LevelOneDataExt.imaxRe n x.data vstrg.offset vstrg.inc h, sorry_proof⟩

def imaxIm (_x : K^[n]) (h : n ≠ 0) : Fin n := ⟨0, by omega⟩

def iminRe (x : K^[n]) (h : n ≠ 0) : Fin n :=
  ⟨LevelOneDataExt.iminRe n x.data vstrg.offset vstrg.inc h, sorry_proof⟩

def iminIm (_x : K^[n]) (h : n ≠ 0) : Fin n := ⟨0, by omega⟩

def mul (x y : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.mul n x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, sorry_proof⟩

def div (x : K^[n]) (y : K^[n]') : K^[n]' :=
  ⟨LevelOneDataExt.div n x.data vstrg.offset vstrg.inc y.data vstrg.offset vstrg.inc, sorry_proof⟩

def inv (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.inv n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def abs (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.abs n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def sqrt (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.sqrt n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def exp (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.exp n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def log (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.log n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def sin (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.sin n x.data vstrg.offset vstrg.inc, sorry_proof⟩

def cos (x : K^[n]) : K^[n] :=
  ⟨LevelOneDataExt.cos n x.data vstrg.offset vstrg.inc, sorry_proof⟩



/- Level 1 derived operations -/

/-- Turn `x` into vector with normal storage -/
def toNormal (x : K^[n]) : DenseVector Array .normal n K :=
  let y : DenseVector Array .normal n K := const n .normal 0 -- can we avoid zero initialization?
  ⟨LevelOneData.copy n x.data vstrg.offset vstrg.inc y.data 0 1, sorry_proof⟩

/-- Set `x` to `y`, modifies `x` inplace if possible -/
def setArray (x : K^[n]) (y : K^[n]') : K^[n] :=
  ⟨LevelOneData.copy n y.data vstrg'.offset vstrg'.inc x.data vstrg.offset vstrg.inc, sorry_proof⟩
