import LeanBLAS.FFI.FloatArray

namespace BLAS.CBLAS

/-! # CBLAS Level 1 FFI Bindings for Float64

This module provides low-level FFI (Foreign Function Interface) bindings to CBLAS Level 1
operations for double-precision floating-point numbers (Float64).

## Overview

Level 1 BLAS operations work with vectors and have O(n) complexity. This module exposes
the C interface directly to Lean through the `@[extern]` attribute, allowing zero-overhead
calls to optimized BLAS implementations.

## FFI Design

Each function is declared as `opaque` with an `@[extern]` attribute pointing to the
corresponding C function. The bindings handle:
- Conversion between Lean's USize and C's size_t/int
- Direct memory access through Float64Array pointers
- Proper alignment and layout for BLAS compatibility

## Naming Convention

Functions follow the BLAS naming convention:
- `d` prefix: double precision (Float64)
- Operation name: dot, axpy, scal, etc.
- Example: `ddot` = double-precision dot product

## Performance Notes

These are direct FFI calls with minimal overhead:
- No memory copying (arrays passed by reference)
- No runtime type checking (handled at Lean level)
- Direct access to optimized BLAS kernels
-/


/-- ddot

summary: computes the dot product of two vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- incY: the increment for the elements of Y
- offY: starting offset of elements of Y

outputs:
- the dot product of X and Y

-/
@[extern "leanblas_cblas_ddot"]
opaque ddot (N : USize) (X : @& Float64Array) (offX incX : USize) (Y : @& Float64Array) (offY incY : USize) : Float



/-- dnrm2

summary: computes the Euclidean norm of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the Euclidean norm of X

C interface
```
double cblas_dnrm2(const int N, const double *X, const int incX);
```
-/
@[extern "leanblas_cblas_dnrm2"]
opaque dnrm2 (N : USize) (X : @& Float64Array) (offX incX : USize) : Float


/-- dasum

summary: computes the sum of the absolute values of the elements of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the sum of the absolute values of the elements of X

C interface
```
double cblas_dasum(const int N, const double *X, const int incX);
```
-/
@[extern "leanblas_cblas_dasum"]
opaque dasum (N : USize) (X : @& Float64Array) (offX incX : USize) : Float


/-- idamax

summary: finds the index of the element with the largest absolute value in a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the index of the element with the largest absolute value in X

C interface
```
int cblas_idamax(const int N, const double *X, const int incX);
```
-/
@[extern "leanblas_cblas_idamax"]
opaque idamax (N : USize) (X : @& Float64Array) (offX incX : USize) : USize


/-- dswap

summary: swaps the elements of two vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: X and Y with their elements swapped

C interface
```
void cblas_dswap(const int N, double *X, const int incX, double *Y, const int incY);
```
-/
@[extern "leanblas_cblas_dswap"]
opaque dswap (N : USize) (X : Float64Array) (offX incX : USize) (Y : Float64Array) (offY incY : USize) : Float64Array × Float64Array


/-- dcopy

summary: copies the elements of a vector to another vector

inputs:
- N: the number of elements in the vectors
- X: the vector to be copied
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the vector to be copied to
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y with the elements of X copied to it

C interface
```
void cblas_dcopy(const int N, const double *X, const int incX, double *Y, const int incY);
```
-/
@[extern "leanblas_cblas_dcopy"]
opaque dcopy (N : USize) (X : @& Float64Array) (offX incX : USize) (Y : Float64Array) (offY incY : USize) : Float64Array


/-- daxpy

summary: computes the sum of a vector and the product of a scalar and another vector

inputs:
- N: the number of elements in the vectors
- alpha: the scalar
- X: the vector to be scaled and added
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the vector to be added to
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y with the sum of X and the product of alpha and Y

C interface
```
void cblas_daxpy(const int N, const double alpha, const double *X,
                 const int incX, double *Y, const int incY);
```
-/
@[extern "leanblas_cblas_daxpy"]
opaque daxpy (N : USize) (a : Float) (X : @& Float64Array) (offX incX : USize) (Y : Float64Array) (offY incY : USize) : Float64Array


/-- drotg

summary: constructs a Givens rotation

inputs:
- a: the first element of the input vector
- b: the second element of the input vector

outputs:
- c: the cosine of the rotation
- s: the sine of the rotation
- r: the norm of the input vector
- z: the scaling factor


C interface
```
void cblas_drotg(double *a, double *b, double *c, double *s);
```
-/
@[extern "leanblas_cblas_drotg"]
opaque drotg (a : Float) (b : Float) : (Float × Float × Float × Float)


/-- drotmg

summary: constructs a modified Givens rotation

inputs:
- d1: the first element of the input vector
- d2: the second element of the input vector
- x1: the first element of the output vector


outputs: d1, d2, x1, y1, and P with the modified Givens rotation applied to them

C interface
```
void cblas_drotmg(double *d1, double *d2, double *b1, const double b2, double *P);
```
-/
@[extern "leanblas_cblas_drotmg"]
opaque drotmg (d1 : Float) (d2 : Float) (b1 : Float) (b2 : Float) : (Float × Float × Float × Float × Float)


/-- drot

summary: applies a Givens rotation to a pair of vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y
- c: the cosine of the rotation
- s: the sine of the rotation

outputs: X and Y with the Givens rotation applied to them

C interface
```
void cblas_drot(const int N, double *X, const int incX, double *Y, const int incY,
                const double c, const double s);
```
-/
@[extern "leanblas_cblas_drot"]
opaque drot (N : USize) (X : Float64Array) (offX incX : USize) (Y : Float64Array) (offY incY : USize) (c s : Float) : Float64Array × Float64Array


/-- dscal

summary: scales a vector by a scalar

inputs:
- N: the number of elements in the vector
- alpha: the scalar
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with its elements scaled by alpha

C interface
```
void cblas_dscal(const int N, const double alpha, double *X, const int incX);
```
-/
@[extern "leanblas_cblas_dscal"]
opaque dscal (N : USize) (a : Float) (X : Float64Array) (offX incX : USize) : Float64Array



-- @[instance]
-- axiom cblasLevelOneDoubleAxiom : BLAS.LevelOneSpec Float64Array Float Float

-- instance : BLAS.LevelOne Float64Array Float Float := ⟨⟩


-- class LevelOneDataExt (R K : outParam Type) (Array : Type) [Scalar R K] where
--   const (N : Nat) (a : K) : Array
--   sum (N : Nat) (X : Array) (offX incX : Nat) : K
--   axpby (N : Nat) (a : K) (X : Array) (offX incX : Nat) (b : K)  (Y : Array) (offY incY : Nat) : Array

--   maxRe (N : Nat) (X : Array) (offX incX : Nat) : R
--   maxIm (N : Nat) (X : Array) (offX incX : Nat) : R
--   minRe (N : Nat) (X : Array) (offX incX : Nat) : R
--   minIm (N : Nat) (X : Array) (offX incX : Nat) : R

--   /- Element wise operations -/
--   mul (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
--   div (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : Array
--   inv (N : Nat) (X : Array) (offX incX : Nat) : Array
--   abs (N : Nat) (X : Array) (offX incX : Nat) : Array
--   sqrt (N : Nat) (X : Array) (offX incX : Nat) : Array
--   exp (N : Nat) (X : Array) (offX incX : Nat) : Array
--   log (N : Nat) (X : Array) (offX incX : Nat) : Array
--   sin (N : Nat) (X : Array) (offX incX : Nat) : Array
--   cos (N : Nat) (X : Array) (offX incX : Nat) : Array



/-- dconst

summary: creates a vector with a constant value

inputs:
- N: the number of elements in the vector
- alpha: the constant value

outputs: a vector with all elements equal to alpha
-/
@[extern "leanblas_cblas_dconst"]
opaque dconst (N : USize) (alpha : Float) : Float64Array


/-- dsum

summary: computes the sum of the elements of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the sum of the elements of X
-/
@[extern "leanblas_cblas_dsum"]
opaque dsum (N : USize) (X : @&Float64Array) (offX : USize) (incX : USize) : Float


/-- daxpby

summary: computes `alpha*X + beta*Y`

inputs:
- N: the number of elements in the vectors
- alpha: the scalar
- X: the vector to be scaled and added
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- beta: the scalar
- Y: the vector to be added to
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: `alpha*X + beta*Y` at appropriate indices
-/
@[extern "leanblas_cblas_daxpby"]
opaque daxpby (N : USize) (alpha : Float) (X : Float64Array) (offX : USize) (incX : USize)
                          (beta : Float)  (Y : Float64Array) (offY : USize) (incY : USize) : Float64Array

/-- scaladd

summary: computes `alpha*X + beta`

inputs:
- N: the number of elements in the vectors
- alpha: the scalar
- beta: the scalar
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: `alpha*X + beta` at appropriate indices
-/
@[extern "leanblas_cblas_dscaladd"]
opaque dscaladd (N : USize) (alpha : Float) (X : Float64Array) (offX : USize) (incX : USize) (beta : Float) : Float64Array

/-- dimaxRe

summary: finds the index of the element with the largest real part in a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the index of the element with the largest real part in X

-/
@[extern "leanblas_cblas_dimax_re"]
opaque dimaxRe (N : USize) (X : @&Float64Array) (offX : USize) (incX : USize) : USize


/-- diminRe

summary: finds the index of the element with the smallest real part in a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs:
- the index of the element with the smallest real part in X
-/
@[extern "leanblas_cblas_dimin_re"]
opaque diminRe (N : USize) (X : @&Float64Array) (offX : USize) (incX : USize) : USize


/-- dmul

summary: computes the element-wise product of two vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: the element-wise product of X and Y

-/
@[extern "leanblas_cblas_dmul"]
opaque dmul (N : USize) (X : Float64Array) (offX : USize) (incX : USize) (Y : Float64Array) (offY : USize) (incY : USize) : Float64Array


/-- ddiv

summary: computes the element-wise division of two vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y

outputs: the element-wise division of X and Y

-/
@[extern "leanblas_cblas_ddiv"]
opaque ddiv (N : USize) (X : Float64Array) (offX : USize) (incX : USize) (Y : Float64Array) (offY : USize) (incY : USize) : Float64Array


/-- dinv

summary: computes the element-wise inverse of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise inverse of X

-/
@[extern "leanblas_cblas_dinv"]
opaque dinv (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dabs

summary: computes the element-wise absolute value of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise absolute value of X

-/
@[extern "leanblas_cblas_dabs"]
opaque dabs (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dsqrt

summary: computes the element-wise square root of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise square root of X

-/
@[extern "leanblas_cblas_dsqrt"]
opaque dsqrt (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dexp

summary: computes the element-wise exponential of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise exponential of X

-/
@[extern "leanblas_cblas_dexp"]
opaque dexp (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dlog

summary: computes the element-wise natural logarithm of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise natural logarithm of X

-/
@[extern "leanblas_cblas_dlog"]
opaque dlog (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dsin

summary: computes the element-wise sine of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise sine of X

-/
@[extern "leanblas_cblas_dsin"]
opaque dsin (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array


/-- dcos

summary: computes the element-wise cosine of a vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the element-wise cosine of X

-/
@[extern "leanblas_cblas_dcos"]
opaque dcos (N : USize) (X : Float64Array) (offX : USize) (incX : USize) : Float64Array
