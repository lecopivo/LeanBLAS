import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanBLAS.Scalar

namespace BLAS

class LevelOneData (R K : outParam Type) (Array : Type) where

  size (X : Array) : Nat
  get (X : Array) (i : Nat) : K
  set (X : Array) (i : Nat) (v : K) : Array
  ofFn (f : Fin n → K) : Array

  /-- dot product of two vectors
      N : number of elements
      X : input vector
      offX : offset of the first element of X
      incX : stride of X
      Y : input vector
      offY : offset of the first element of Y
      incY : stride of Y

      The result is the dot product of the two vectors -/
  dot (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY IncY : Nat) : K

  /-- Euclidean norm of a vector
      N : number of elements
      X : input vector
      offX : offset of the first element of X
      incX : stride of X

      The result is the Euclidean norm of the vector -/
  nrm2 (N : Nat) (X : Array) (offX incX : Nat) : R

  /-- sum of the absolute values of the elements of a vector
      N : number of elements
      X : input vector
      offX : offset of the first element of X
      incX : stride of X

      The result is the sum of the absolute values of the elements of the vector -/
  asum (N : Nat) (X : Array) (offX incX : Nat) : R
  /-- index of the element with maximum absolute value
      N : number of elements
      X : input vector
      offX : offset of the first element of X
      incX : stride of X

      The result is the index of the element with maximum absolute value -/
  iamax (N : Nat) (X : Array) (offX incX : Nat) : Nat


  swap (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array × Array

  /-- copy elements from one vector to another
      N : number of elements
      X : input vector
      offX : offset of the first element of X
      incX : stride of X
      Y : output vector
      offY : offset of the first element of Y
      incY : stride of Y

      The elements of Y are replaced by the elements of X -/
  copy (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array

  /-- scale a vector by a constant
      N : number of elements
      α : scalar
      X : input/output vector
      offX : offset of the first element of X
      incX : stride of X

      The elements of X are replaced by α times the elements of X -/
  axpy (N : Nat) (α : K) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array

  rotg (a b : K) : R × K × K × K
  rotmg (d1 d2 b1 b2 : R) : R × R × R × R × K
  rot (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) (c s : K) : Array × Array

  scal (N : Nat) (α : K) (X : Array) (offX incX : Nat) : Array

class LevelOneDataExt (R K : outParam Type) (Array : Type) where
  const (N : Nat) (a : K) : Array
  sum (N : Nat) (X : Array) (offX incX : Nat) : K
  axpby (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K)  (Y : Array) (offY incY : Nat) : Array
  /-- return `a•x + b` -/
  scaladd (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K) : Array

  imaxRe (N : Nat) (X : Array) (offX incX : Nat) : Nat
  imaxIm (N : Nat) (X : Array) (offX incX : Nat) : Nat
  iminRe (N : Nat) (X : Array) (offX incX : Nat) : Nat
  iminIm (N : Nat) (X : Array) (offX incX : Nat) : Nat

  /- Element wise operations -/
  mul (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
  div (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
  inv (N : Nat) (X : Array) (offX incX : Nat) : Array
  abs (N : Nat) (X : Array) (offX incX : Nat) : Array
  sqrt (N : Nat) (X : Array) (offX incX : Nat) : Array
  exp (N : Nat) (X : Array) (offX incX : Nat) : Array
  log (N : Nat) (X : Array) (offX incX : Nat) : Array
  sin (N : Nat) (X : Array) (offX incX : Nat) : Array
  cos (N : Nat) (X : Array) (offX incX : Nat) : Array



export LevelOneData (get dot nrm2 asum iamax swap copy axpy rotg rotmg rot scal)


section

variable {R C : Type} {Array : Type} [Scalar R R] [Scalar R C] [BLAS.LevelOneData R C Array]

open BLAS.LevelOneData

/-- `i` is in bounds of array `X` when accesseed with offset `offX` and increment `incX` -/
structure InBounds (X : Array) (offX incX) (i : Nat) where
  valid_inc : 0 < incX
  in_oubnds : offX + i * incX < size X

end

open RCLike in
noncomputable
def toComplex {K} [RCLike K] (x : K) : ℂ := algebraMap ℝ ℂ (re x) + algebraMap ℝ ℂ (im x) * I

open RCLike in
noncomputable
def toReal {K} [RCLike K] (x : K) : ℝ := re x

open RCLike in
def fromComplex {K} [RCLike K] (z : ℂ) : K := algebraMap ℝ K (z.re) + algebraMap ℝ K (z.im) * I

open RCLike in
def fromReal {K} [RCLike K] (x : ℝ) : K := algebraMap ℝ K x

@[simp]
theorem fromComplex_toComplex {K} [RCLike K] (x : K) : fromComplex (toComplex x) = x := by
  simp [fromComplex, toComplex]

set_option pp.coercions false in
@[simp]
theorem toComplex_fromComplex_real {K} [RCLike K] (x : ℝ) :
    toComplex (fromComplex (K:=K) x) = x := by
  simp [fromComplex, toComplex]

@[simp]
theorem fromReal_toReal {K} [RCLike K] (x : K) (h : RCLike.im x = 0) :
    fromReal (toReal x) = x := by
  conv => rhs; rw[←RCLike.re_add_im_ax x]
  simp [fromReal, toReal,h]

@[simp]
theorem toReal_fromReal {K} [RCLike K] (x : ℝ) : toReal (fromReal (K:=K) x) = x :=
  by simp [fromReal, toReal]

open BLAS.LevelOneData ComplexConjugate in
class LevelOneSpec (R C : Type) (Array : Type) [RCLike R] [RCLike C] [BLAS.LevelOneData R C Array] : Prop  where

  ofFn_size (f : Fin n → C) :
    size (ofFn (Array:=Array) f) = n

  dot_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    (∀ i : Fin N, InBounds Y offY incY i)
    →
    (dot N X offX incX Y offY incY)
    =
    ∑ i : Fin N, conj (get X (offX + i.1*incX)) * get Y (offY + i.1*incY)


  norm2_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    toReal (nrm2 N X offX incX)
    =
    √(∑ i : Fin N, ‖toComplex (get X (offX + i.1*incX))‖^2 )


  asum_spec (N : Nat) (X : Array) (offX incX : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    toReal (asum N X offX incX)
    =
    ∑ i : Fin N, ‖toComplex (get X (offX + i.1*incX))‖

  iamax_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    iamax N X offX incX
    =
    ((List.ofFn (fun i : Fin N => i)).argmax (fun i => ‖toComplex (get X (offX + i*incX))‖)).getD 0

  swap_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    swap N X offX incX Y offY incX
    =
    (copy N Y offY incY X offX incX,
     copy N X offX incX Y offY incY)

  swap_size_x (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (swap N X offX incX Y offY incX).1
    =
    size X

  swap_size_y (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (swap N X offX incX Y offY incX).2
    =
    size Y

  copy_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size Y →
      get (copy N X offX incX Y offY incY) i
      =
      if (i - offY) % incY = 0 then
        let j := ((i - offY) / incY) * incX + offX
        get X j
      else
        get Y i

  copy_size (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (copy N X offX incX Y offY incY)
    =
    size Y

  axpy_spec (N : Nat) (α : C) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size Y →
      get (axpy N α X offX incX Y offY incY) i
      =
      if (i - offY) % incY = 0 then
        let j := ((i - offY) / incY) * incX + offX
        get Y i + α * get X j
      else
        get Y i

  axpy_size (N : Nat) (α : C) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (axpy N α X offX incX Y offY incY)
    =
    size Y

  scal_spec (N : Nat) (α : C) (X : Array) (offX incX : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    ∀ i : Nat, i < size X →
      get (scal N α X offX incX) i
      =
      if (i - offX) % incX = 0 then α * get X i else get X i

  scal_size (N : Nat) (α : C) (X : Array) (offX incX : Nat) :
    size (scal N α X offX incX)
    =
    size X


open BLAS.LevelOneData BLAS.LevelOneDataExt in
class LevelOneExtSpec (R K : Type) (Array : Type) [RCLike R] [RCLike K]
    [BLAS.LevelOneData R K Array] [BLAS.LevelOneDataExt R K Array] : Prop  where
  const_spec (N : Nat) (a : K) :
    ∀ i, get (const (Array:=Array) N a) i = a
  sum_spec (N : Nat) (X : Array) (offX incX : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    sum N X offX incX
    =
    ∑ i : Fin N, get X (offX + i.1*incX)

  axpby_spec (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K)  (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size Y →
      get (axpby N a X offX incX b Y offY incY) i
      =
      if (i - offY) % incY = 0 then
        let j := ((i - offY) / incY) * incX + offX
        a * get X j + b * get Y i
      else
        get Y i

  /-- return `a•x + b` -/
  scaladd_spec (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (scaladd N a X offX incX b) i
      =
      if (i - offX) % incX = 0 then a * get X i + b else get X i

  imaxRe_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    imaxRe N X offX incX
    =
    ((List.ofFn (fun i : Fin N => i)).argmax (fun i => RCLike.re (get X (offX + i*incX)))).getD 0

  imaxIm_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    imaxIm N X offX incX
    =
    ((List.ofFn (fun i : Fin N => i)).argmax (fun i => RCLike.im (get X (offX + i*incX)))).getD 0

  iminRe_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    iminRe N X offX incX
    =
    ((List.ofFn (fun i : Fin N => i)).argmin (fun i => RCLike.re (get X (offX + i*incX)))).getD 0

  iminIm_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    iminIm N X offX incX
    =
    ((List.ofFn (fun i : Fin N => i)).argmin (fun i => RCLike.im (get X (offX + i*incX)))).getD 0

  /- Element wise operations -/
  mul_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size X →
      get (mul N X offX incX Y offY incY) i
      =
      if (i - offX) % incX = 0 then
        let j := ((i - offX) / incX) * incY + offY
        get X i * get Y j
      else
        get X i

  mul_size (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (mul N X offX incX Y offY incY)
    =
    size X

  div_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size X →
      get (div N X offX incX Y offY incY) i
      =
      if (i - offX) % incX = 0 then
        let j := ((i - offX) / incX) * incY + offY
        get X i / get Y j
      else
        get X i

  div_size (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (div N X offX incX Y offY incY)
    =
    size X

  inv_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (inv N X offX incX) i
      =
      if (i - offX) % incX = 0 then 1 / get X i else get X i

  inv_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (inv N X offX incX)
    =
    size X

  abs_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (abs N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromReal ‖toComplex (get X i)‖ else get X i

  abs_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (abs N X offX incX)
    =
    size X

  sqrt_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (sqrt N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromComplex ((toComplex (get X i))^(1/2:ℂ)) else get X i

  sqrt_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (sqrt N X offX incX)
    =
    size X

  exp_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (exp N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromComplex (toComplex (get X i)).exp else get X i

  exp_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (exp N X offX incX)
    =
    size X

  log_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (log N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromComplex (toComplex (get X i)).log else get X i

  log_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (log N X offX incX)
    =
    size X

  sin_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (sin N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromComplex (toComplex (get X i)).sin else get X i

  sin_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (sin N X offX incX)
    =
    size X

  cos_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (cos N X offX incX) i
      =
      if (i - offX) % incX = 0 then fromComplex (toComplex (get X i)).cos else get X i

  cos_size (N : Nat) (X : Array) (offX incX : Nat) :
    size (cos N X offX incX)
    =
    size X


attribute [simp]
  LevelOneSpec.ofFn_size
  LevelOneSpec.swap_size_x
  LevelOneSpec.swap_size_y
  LevelOneSpec.copy_size
  LevelOneSpec.axpy_size
  LevelOneSpec.scal_size


class LevelOne (R K : Type) (Array : Type) [RCLike R] [RCLike K]
    extends BLAS.LevelOneData R K Array, BLAS.LevelOneSpec R K Array

class LevelOneExt (R K : Type) (Array : Type) [RCLike R] [RCLike K] [BLAS.LevelOneData R K Array]
    extends BLAS.LevelOneDataExt R K Array, BLAS.LevelOneExtSpec R K Array
