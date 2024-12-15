import LeanBLAS.Spec.LevelTwo

namespace BLAS


/-- dgemv

summary: computes the product of a matrix and a vector

inputes:
- N: the number of rows in the matrix
- M: the number of columns in the matrix
- alpha: the scalar
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- beta: the scalar
- Y: the vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y with the product of A and X

C interface
```
void cblas_dgemv(const enum CBLAS_ORDER Order, const enum C, const int M, const int N,
                 const double alpha, const double *A, const int lda, const double *X,
                 const int incX, const double beta, double *Y, const int incY);
```
-/
@[extern "leanblas_cblas_dgemv"]
opaque dgemv (order : Order) (transA : Transpose) (N : USize) (M : USize) (alpha : Float)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : @& FloatArray) (offX incX : USize) (beta : Float)
    (Y : FloatArray) (offY incY : USize) : FloatArray



/-- dgbmv

summary: computes the product of a band matrix and a vector

inputs:
- N: the number of rows in the matrix
- M: the number of columns in the matrix
- KL: the number of subdiagonals in the matrix
- KU: the number of superdiagonals in the matrix
- alpha: the scalar
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- beta: the scalar
- Y: the vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y

outputs: Y with the product of A and X
-/
@[extern "leanblas_cblas_dgbmv"]
opaque dbmv (order : Order) (transA : Transpose) (N : USize) (M : USize) (KL KU : USize) (alpha : Float)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : @& FloatArray) (offX incX : USize) (beta : Float)
    (Y : FloatArray) (offY incY : USize) : FloatArray


/-- dtrmv

summary: computes the product of a triangular matrix and a vector

inputs:
- N: the number of rows in the matrix
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the product of A and X
-/
@[extern "leanblas_cblas_dtrmv"]
opaque dtrmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : USize)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray


/-- dtbmv

summary: computes the product of a triangular band matrix and a vector

inputs:
- N: the number of rows in the matrix
- K: the number of subdiagonals in the matrix
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the product of A and X
-/
@[extern "leanblas_cblas_dtbmv"]
opaque dtbmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : USize)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray


/-- dtpmv

summary: computes the product of a triangular packed matrix and a vector

inputs:
- N: the number of rows in the matrix
- A: the matrix
- offA: starting offset of elements of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the product of A and X
-/
@[extern "leanblas_cblas_dtpmv"]
opaque dtpmv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : USize)
    (A : @& FloatArray) (offA : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray


/-- dtrsv

summary: solves a triangular system of equations

inputs:
- N: the number of rows in the matrix
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the solution of the system
-/
@[extern "leanblas_cblas_dtrsv"]
opaque dtrsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : USize)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray


/-- dtbsv

summary: solves a triangular band system of equations

inputs:
- N: the number of rows in the matrix
- K: the number of subdiagonals in the matrix
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the solution of the system
-/
@[extern "leanblas_cblas_dtbsv"]
opaque dtbsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N K : USize)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray


/-- dtpsv

summary: solves a triangular packed system of equations

inputs:
- N: the number of rows in the matrix
- A: the matrix
- offA: starting offset of elements of A
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X

outputs: X with the solution of the system
-/
@[extern "leanblas_cblas_dtpsv"]
opaque dtpsv (order : Order) (uplo : UpLo)
    (transA : Transpose) (diag : Bool) (N : USize)
    (A : @& FloatArray) (offA : USize)
    (X : FloatArray) (offX incX : USize) : FloatArray
