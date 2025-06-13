/-
Copyright (c) 2024 The LeanBLAS Authors. All rights reserved.
Released under the Apache 2.0 license as described in the repository's LICENSE file.
Authors: The LeanBLAS Development Team
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.NormedSpace.RCLike

import LeanBLAS.Spec.Scalar

-- Enable missing documentation linter for this file
set_option linter.missingDocs true

/-!
## Level 1 BLAS Operations

This module defines the interface for Level 1 BLAS operations, which are vector-vector operations.
Level 1 BLAS includes operations like dot products, norms, vector scaling, and vector addition.

The operations are defined abstractly over an `Array` type with scalar types `R` (real) and `K` (field).
-/

namespace BLAS

/--
Core Level 1 BLAS operations interface.

This class defines the fundamental vector operations that form the basis of Level 1 BLAS.
Implementations should provide efficient algorithms for these operations, typically
leveraging hardware-optimized libraries.

## Type Parameters
- `Array`: The array/vector type
- `R`: The real number type (for norms and real-valued results)
- `K`: The field type (can be real or complex)

## Implementation Notes

Many operations use offset and stride parameters:
- `off`: Starting index in the array
- `inc`: Stride between consecutive elements (can be negative for reverse traversal)

This allows working with subvectors and non-contiguous data layouts.
-/
class LevelOneData (Array : Type*) (R K : outParam Type*) where

  /-- Get the size/length of a vector. -/
  size (X : Array) : Nat
  
  /-- Get the element at index `i` from vector `X`. -/
  get (X : Array) (i : Nat) : K
  -- set (X : Array) (i : Nat) (v : K) : Array
  -- ofFn (f : Fin n → K) : Array

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


  /-- 
  Swap elements between two vectors.
  
  Exchanges `N` elements between vectors `X` and `Y` using the specified offsets and strides.
  Returns the pair of modified vectors.
  -/
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

  /-- add a multiple of a vector to another vector
      N : number of elements
      α : scalar
      X : input vector
      offX : offset of the first element of X
      incX : stride of X
      Y : output vector
      offY : offset of the first element of Y
      incY : stride of Y

      The elements of Y are replaced by `Y + α•X`  -/
  axpy (N : Nat) (α : K) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array

  /-- 
  Generate Givens rotation parameters.
  
  Given scalars `a` and `b`, computes rotation parameters to zero out `b`.
  Returns `(r, c, s, z)` where `c` and `s` define the rotation.
  -/
  rotg (a b : K) : R × K × K × K
  
  /-- 
  Generate modified Givens rotation parameters.
  
  Computes rotation parameters for the modified Givens transformation.
  Returns updated diagonal elements and rotation parameters.
  -/
  rotmg (d1 d2 b1 b2 : R) : R × R × R × R × K
  
  /-- 
  Apply Givens rotation to vectors.
  
  Applies the rotation defined by `c` (cosine) and `s` (sine) to vectors `X` and `Y`.
  Returns the pair of rotated vectors.
  -/
  rot (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) (c s : K) : Array × Array

  /-- 
  Scale a vector by a scalar.
  
  Multiplies `N` elements of vector `X` by scalar `α`, starting at offset `offX`
  with stride `incX`. Returns the scaled vector.
  -/
  scal (N : Nat) (α : K) (X : Array) (offX incX : Nat) : Array

/--
Extended Level 1 BLAS operations.

This class provides additional vector operations that are commonly needed but not part
of the standard BLAS specification. These operations extend the functionality to cover
more use cases in numerical computing.

## Type Parameters
- `Array`: The array/vector type  
- `R`: The real number type
- `K`: The field type (real or complex)
-/
class LevelOneDataExt (Array : Type*) (R K : outParam Type*) where
  /-- Create a constant vector of length `N` with all elements equal to `a`. -/
  const (N : Nat) (a : K) : Array
  
  /-- Compute the sum of elements in a vector. -/
  sum (N : Nat) (X : Array) (offX incX : Nat) : K
  
  /-- Generalized AXPY: compute `Y := a•X + b•Y`. -/
  axpby (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K)  (Y : Array) (offY incY : Nat) : Array
  /-- return `a•x + b` -/
  scaladd (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K) : Array

  /-- Index of element with maximum real part (requires non-empty vector). -/
  imaxRe (N : Nat) (X : Array) (offX incX : Nat) (h : N ≠ 0) : Nat
  
  /-- Index of element with maximum imaginary part (requires non-empty vector). -/
  imaxIm (N : Nat) (X : Array) (offX incX : Nat) (h : N ≠ 0) : Nat
  
  /-- Index of element with minimum real part (requires non-empty vector). -/
  iminRe (N : Nat) (X : Array) (offX incX : Nat) (h : N ≠ 0) : Nat
  
  /-- Index of element with minimum imaginary part (requires non-empty vector). -/
  iminIm (N : Nat) (X : Array) (offX incX : Nat) (h : N ≠ 0) : Nat

  /- Element wise operations -/
  /-- Element-wise multiplication: Return `Y` with elements `yᵢ := xᵢ * yᵢ`. -/
  mul (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
  
  /-- Element-wise division: Return `Y` with elements `yᵢ := xᵢ / yᵢ`. -/
  div (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
  
  /-- Element-wise reciprocal: Return vector with elements `1 / xᵢ`. -/
  inv (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise absolute value: Return vector with elements `|xᵢ|`. -/
  abs (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise square root: Return vector with elements `√xᵢ`. -/
  sqrt (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise exponential: Return vector with elements `exp(xᵢ)`. -/
  exp (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise logarithm: Return vector with elements `log(xᵢ)`. -/
  log (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise sine: Return vector with elements `sin(xᵢ)`. -/
  sin (N : Nat) (X : Array) (offX incX : Nat) : Array
  
  /-- Element-wise cosine: Return vector with elements `cos(xᵢ)`. -/
  cos (N : Nat) (X : Array) (offX incX : Nat) : Array



-- Export commonly used Level 1 BLAS operations for easier access
export LevelOneData (get dot nrm2 asum iamax swap copy axpy rotg rotmg rot scal)


section

variable {R C : Type*} {Array : Type*} [RCLike R] [RCLike K] [BLAS.LevelOneData Array R C]

open BLAS.LevelOneData

/-- 
Predicate that ensures an index `i` is within bounds when accessing array `X` 
with offset `offX` and stride `incX`.

This is used to ensure memory safety in BLAS operations.
-/
structure InBounds (X : Array) (offX incX) (i : Nat) where
  /-- The stride must be positive. -/
  valid_inc : 0 < incX
  /-- The computed index must be within the array bounds. -/
  in_bounds : offX + i * incX < size X

end

open BLAS.LevelOneData ComplexConjugate in
/--
Mathematical specifications for Level 1 BLAS operations.

This class defines the precise mathematical behavior that lawful BLAS implementations
must satisfy. Each operation is specified in terms of its mathematical definition,
allowing formal verification of correctness.

## Type Parameters
- `Array`: The array type
- `R`: Real number type with `RCLike` instance
- `C`: Complex/field type with `RCLike` instance

## Implementation Note

These specifications use exact mathematical definitions. Floating-point implementations
may not satisfy these exactly due to rounding errors, but they serve as the ideal
behavior that implementations approximate.
-/
class LevelOneSpec (Array : Type*) (R C : outParam Type*) [RCLike R] [RCLike C] [LevelOneData Array R C] : Prop  where

  -- ofFn_size (f : Fin n → C) :
  --   size (ofFn (Array:=Array) f) = n

  /-- The dot product computes the sum of conjugate(xᵢ) * yᵢ over all elements. -/
  dot_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    (∀ i : Fin N, InBounds Y offY incY i)
    →
    (dot N X offX incX Y offY incY)
    =
    ∑ (i : Fin N), conj (get X (offX + i.1*incX)) * get Y (offY + i.1*incY)


  /-- The 2-norm (Euclidean norm) is the square root of the sum of squared magnitudes. -/
  norm2_spc (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    (nrm2 N X offX incX)
    =
    Real.sqrt (∑ i : Fin N, (toComplex (get X (offX + i.1*incX))).normSq)


  /-- The absolute sum computes the sum of |real(xᵢ)| + |imag(xᵢ)| over all elements. -/
  asum_spec (N : Nat) (X : Array) (offX incX : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    (asum N X offX incX)
    =
    (∑ (i : Fin N), let x := (toComplex (get X (offX + i.1*incX))); |x.re| + |x.im|)

  /-- iamax finds the index of the element with maximum absolute value.
      Returns the index i such that |X[i]| ≥ |X[j]| for all valid j.
      If multiple elements have the same maximum absolute value, returns the first index. -/
  iamax_spec (N : Nat) (X : Array) (offX incX : Nat) :
    InBounds X offX incX (N-1)
    →
    N > 0
    →
    ∃ (i : Fin N), 
      (∀ (j : Fin N), |toReal (get X (offX + i.1*incX))| ≥ |toReal (get X (offX + j.1*incX))|)
      ∧
      (∀ (j : Fin N), j.1 < i.1 → |toReal (get X (offX + j.1*incX))| < |toReal (get X (offX + i.1*incX))|)

  /-- Swap exchanges elements between two vectors. -/
  swap_spec (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    InBounds X offX incX (N-1)
    →
    InBounds Y offY incY (N-1)
    →
    swap N X offX incX Y offY incX
    =
    (copy N Y offY incY X offX incX,
     copy N X offX incX Y offY incY)

  /-- Swap preserves the size of the first array. -/
  swap_size_x (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (swap N X offX incX Y offY incX).1
    =
    size X

  /-- Swap preserves the size of the second array. -/
  swap_size_y (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (swap N X offX incX Y offY incX).2
    =
    size Y

  /-- Copy transfers elements from X to Y, preserving elements of Y not in the target range. -/
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

  /-- Copy preserves the size of the target array. -/
  copy_size (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (copy N X offX incX Y offY incY)
    =
    size Y

  /-- AXPY computes Y := α•X + Y element-wise. -/
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

  /-- AXPY preserves the size of the output array. -/
  axpy_size (N : Nat) (α : C) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) :
    size (axpy N α X offX incX Y offY incY)
    =
    size Y

  -- rotg_spec (a b : C) :
  --   rotg a b
  --   =
  --   sorry

  -- rogmg
  -- rot

  /-- SCAL multiplies vector elements by a scalar: X := α•X. -/
  scal_spec (N : Nat) (α : C) (X : Array) (offX incX : Nat) :
    (∀ i : Fin N, InBounds X offX incX i)
    →
    ∀ i : Nat, i < size X →
      get (scal N α X offX incX) i
      =
      if (i - offX) % incX = 0 then α * get X i else get X i

  /-- SCAL preserves the size of the array. -/
  scal_size (N : Nat) (α : C) (X : Array) (offX incX : Nat) :
    size (scal N α X offX incX)
    =
    size X

attribute [simp]
  -- LevelOneSpec.ofFn_size
  LevelOneSpec.swap_size_x
  LevelOneSpec.swap_size_y
  LevelOneSpec.copy_size
  LevelOneSpec.axpy_size
  LevelOneSpec.scal_size


/-- 
Combines Level 1 BLAS data operations with their mathematical specifications.

This class provides both the operations and their correctness properties,
ensuring that implementations satisfy the expected mathematical behavior.
-/
class LevelOne (Array : Type*) (R K : outParam Type*) [RCLike R] [RCLike K]
    extends BLAS.LevelOneData Array R K, BLAS.LevelOneSpec Array R K
