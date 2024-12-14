/-! Lean bindings to BLAS
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

C interface
```
double cblas_ddot(const int N, const double *X, const int incX,
                  const double *Y, const int incY);
```
-/
@[extern "leanblas_ddot"]
opaque ddot (N : USize) (X : @& FloatArray) (offX incX : USize) (Y : @& FloatArray) (offY incY : USize) : Float

structure Precondition.ddot (N : Nat) (X : @& FloatArray) (offX incX : Nat) (Y : @& FloatArray) (offY incY : Nat) where
  hx_size : offX + 1 + (N-1) * incX ≤ X.size
  hy_size : offY + 1 + (N-1) * incY ≤ X.size


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
@[extern "leanblas_dnrm2"]
opaque dnrm2 (N : USize) (X : @& FloatArray) (offX incX : USize) : Float

structure Precondition.dnrm2 (N : Nat) (X : @& FloatArray) (offX incX : Nat) where
  hx_size : offX + 1 + (N-1) * incX ≤ X.size


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
@[extern "leanblas_dasum"]
opaque dasum (N : USize) (X : @& FloatArray) (offX incX : USize) : Float


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
@[extern "leanblas_idamax"]
opaque idamax (N : USize) (X : @& FloatArray) (offX incX : USize) : USize


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
@[extern "leanblas_dswap"]
opaque dswap (N : USize) (X : FloatArray) (offX incX : USize) (Y : FloatArray) (offY incY : USize) : FloatArray × FloatArray


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
@[extern "leanblas_dcopy"]
opaque dcopy (N : USize) (X : @& FloatArray) (offX incX : USize) (Y : FloatArray) (offY incY : USize) : FloatArray


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
@[extern "leanblas_daxpy"]
opaque daxpy (N : USize) (a : Float) (X : @& FloatArray) (offX incX : USize) (Y : FloatArray) (offY incY : USize) : FloatArray


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
@[extern "leanblas_drotg"]
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
@[extern "leanblas_drotmg"]
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
@[extern "leanblas_drot"]
opaque drot (N : USize) (X : FloatArray) (offX incX : USize) (Y : FloatArray) (offY incY : USize) (c s : Float) : FloatArray × FloatArray


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
@[extern "leanblas_dscal"]
opaque dscal (N : USize) (a : Float) (X : FloatArray) (offX incX : USize) : FloatArray
