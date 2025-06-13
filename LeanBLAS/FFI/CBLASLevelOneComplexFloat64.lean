import LeanBLAS.FFI.FloatArray

namespace BLAS.CBLAS

/-! # CBLAS Level 1 FFI Bindings for ComplexFloat64

This module provides low-level FFI (Foreign Function Interface) bindings to CBLAS Level 1
operations for double-precision complex floating-point numbers (ComplexFloat64).

## Overview

Complex Level 1 BLAS operations work with complex vectors. This module exposes
the C interface for complex arithmetic through the `@[extern]` attribute.

## Complex Number Layout

BLAS uses interleaved storage for complex numbers:
- Each complex number occupies 16 bytes (2 doubles)
- Real part followed immediately by imaginary part
- Arrays are stored as [re₀, im₀, re₁, im₁, ...]

## Naming Convention

Functions follow the BLAS naming convention:
- `z` prefix: double precision complex (ComplexFloat64)
- Operation name: dot, axpy, scal, etc.
- Example: `zdot` = double-precision complex dot product

## Conjugate Operations

Many complex operations have conjugate variants:
- `zdotc`: Conjugate first vector in dot product
- `zdotu`: No conjugation (unconjugated dot product)
-/

/-- zdotc

summary: computes the conjugate dot product of two complex vectors
         result = Σ conj(X[i]) * Y[i]

inputs:
- N: the number of elements in the vectors
- X: the first vector (will be conjugated)
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: the conjugate dot product of X and Y

C interface:
```
void cblas_zdotc_sub(const int N, const void *X, const int incX,
                     const void *Y, const int incY, void *dotc);
```
-/
@[extern "leanblas_cblas_zdotc"]
opaque zdotc (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) 
             (Y : @& ComplexFloat64Array) (offY incY : USize) : ComplexFloat

/-- zdotu

summary: computes the unconjugated dot product of two complex vectors
         result = Σ X[i] * Y[i]

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: the unconjugated dot product of X and Y

C interface:
```
void cblas_zdotu_sub(const int N, const void *X, const int incX,
                     const void *Y, const int incY, void *dotu);
```
-/
@[extern "leanblas_cblas_zdotu"]
opaque zdotu (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) 
             (Y : @& ComplexFloat64Array) (offY incY : USize) : ComplexFloat

/-- dznrm2

summary: computes the Euclidean norm of a complex vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: ||X||₂ = sqrt(Σ |X[i]|²)

C interface:
```
double cblas_dznrm2(const int N, const void *X, const int incX);
```
-/
@[extern "leanblas_cblas_dznrm2"]
opaque dznrm2 (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) : Float

/-- dzasum

summary: computes the sum of absolute values of a complex vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: Σ (|Re(X[i])| + |Im(X[i])|)

C interface:
```
double cblas_dzasum(const int N, const void *X, const int incX);
```
-/
@[extern "leanblas_cblas_dzasum"]
opaque dzasum (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) : Float

/-- izamax

summary: finds the index of the element with the largest absolute value in a complex vector

inputs:
- N: the number of elements in the vector
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: the index of the element with the largest |Re(X[i])| + |Im(X[i])|

C interface:
```
int cblas_izamax(const int N, const void *X, const int incX);
```
-/
@[extern "leanblas_cblas_izamax"]
opaque izamax (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) : USize

/-- zswap

summary: swaps the elements of two complex vectors

inputs:
- N: the number of elements in the vectors
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: X and Y with their elements swapped

C interface:
```
void cblas_zswap(const int N, void *X, const int incX, void *Y, const int incY);
```
-/
@[extern "leanblas_cblas_zswap"]
opaque zswap (N : USize) (X : ComplexFloat64Array) (offX incX : USize) 
             (Y : ComplexFloat64Array) (offY incY : USize) : ComplexFloat64Array × ComplexFloat64Array

/-- zcopy

summary: copies a complex vector to another vector

inputs:
- N: the number of elements in the vectors
- X: the source vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the destination vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y with elements copied from X

C interface:
```
void cblas_zcopy(const int N, const void *X, const int incX, void *Y, const int incY);
```
-/
@[extern "leanblas_cblas_zcopy"]
opaque zcopy (N : USize) (X : @& ComplexFloat64Array) (offX incX : USize) 
             (Y : ComplexFloat64Array) (offY incY : USize) : ComplexFloat64Array

/-- zaxpy

summary: computes Y = alpha*X + Y for complex vectors

inputs:
- N: the number of elements in the vectors
- alpha: the scalar multiplier
- X: the vector to be scaled and added
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the vector to be added to
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y = alpha*X + Y

C interface:
```
void cblas_zaxpy(const int N, const void *alpha, const void *X, const int incX,
                 void *Y, const int incY);
```
-/
@[extern "leanblas_cblas_zaxpy"]
opaque zaxpy (N : USize) (alpha : ComplexFloat) (X : @& ComplexFloat64Array) (offX incX : USize)
             (Y : ComplexFloat64Array) (offY incY : USize) : ComplexFloat64Array

/-- zscal

summary: scales a complex vector by a complex scalar

inputs:
- N: the number of elements in the vector
- alpha: the scalar
- X: the vector to be scaled
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X scaled by alpha

C interface:
```
void cblas_zscal(const int N, const void *alpha, void *X, const int incX);
```
-/
@[extern "leanblas_cblas_zscal"]
opaque zscal (N : USize) (alpha : ComplexFloat) (X : ComplexFloat64Array) (offX incX : USize) : ComplexFloat64Array

/-- zdscal

summary: scales a complex vector by a real scalar

inputs:
- N: the number of elements in the vector
- alpha: the real scalar
- X: the vector to be scaled
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X scaled by alpha

C interface:
```
void cblas_zdscal(const int N, const double alpha, void *X, const int incX);
```
-/
@[extern "leanblas_cblas_zdscal"]
opaque zdscal (N : USize) (alpha : Float) (X : ComplexFloat64Array) (offX incX : USize) : ComplexFloat64Array

end BLAS.CBLAS