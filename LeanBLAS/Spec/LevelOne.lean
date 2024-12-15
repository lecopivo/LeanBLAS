import LeanBLAS.Scalar

namespace BLAS

def sum {X} [OfNat X 0] [Add X] (f : Fin n → X) : X := Fin.foldl (init:=(0:X)) n (fun s i => s + f i)

class LevelOneData (R K : outParam Type) (Array : Type) [Scalar R K] where

  size (X : Array) : Nat
  get (X : Array) (i : Nat) : K

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

export LevelOneData (get dot nrm2 asum iamax swap copy axpy rotg rotmg rot scal)


section

variable {R C : Type} {Array : Type} [Scalar R R] [Scalar R C] [BLAS.LevelOneData R C Array]

open BLAS.LevelOneData

/-- `i` is in bounds of array `X` when accesseed with offset `offX` and increment `incX` -/
structure InBounds (X : Array) (offX incX) (i : Nat) where
  valid_inc : 0 < incX
  in_oubnds : offX + i * incX < size X

end

open BLAS.LevelOneData Scalar in
class BLAS.LevelOneSpec (R C : Type) (Array : Type) [Scalar R R] [Scalar R C] [BLAS.LevelOneData R C Array] : Prop  where


  dot_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    (dot N X offX incX Y offY incY)
    =
    (sum (fun i : Fin N => conj (get X (offX + i.1*incX)) * get Y (offY + i.1*incY)))


  norm2_spc (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    (nrm2 N X offX incX)
    =
    (real (sqrt (sum (fun i : Fin N => let x := get X (offX + i.1*incX); x * conj x))))


  asum_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    (asum N X offX incX)
    =
    (sum (fun i : Fin N => abs (get X (offX + i.1*incX))))

  -- iamax_spec

  swap_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    swap N X offX incX Y offY incX
    =
    (copy N Y offY incY X offX incX,
     copy N X offX incX Y offY incY)


  copy_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    ∀ i : Nat, i < size Y →
      get (axpy N α X offX incX Y offY incY) i
      =
      if (i - offY) % incY = 0 then
        let j := ((i - offY) / incY) * incX + offX
        get X j
      else
        get Y i

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

  -- rotg
  -- rogmg
  -- rot

  scal_spec (N : Nat) (α : C) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    ∀ i : Nat, i < size X →
      get (scal N α X offX incX) i
      =
      if (i - offX) % incX = 0 then α * get X i else get X i



class BLAS.LevelOne (R K : Type) (Array : Type) [Scalar R R] [Scalar R K] [BLAS.LevelOneData R K Array]
    extends BLAS.LevelOneData R K Array, BLAS.LevelOneSpec R K Array