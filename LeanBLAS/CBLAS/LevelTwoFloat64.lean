namespace BLAS.CBLAS


/-- dgemv

summary: computes the product of a matrix and a vector

inputes:
- M: the number of rows in the matrix
- N: the number of columns in the matrix
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
opaque dgemv (order : Order) (transA : Transpose) (M : USize) (N : USize) (alpha : Float)
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



/-- dger

summary: computed rank one update of a matrix

inputs:
- M: the number of rows in the matrix
- N: the number of columns in the matrix
- alpha: the scalar
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A

outputs: A with the outer product of X and Y
-/
@[extern "leanblas_cblas_dger"]
opaque dger (order : Order) (M : USize) (N : USize) (alpha : Float)
    (X : @& FloatArray) (offX incX : USize)
    (Y : @& FloatArray) (offY incY : USize)
    (A : FloatArray) (offA : USize) (lda : USize) : FloatArray


/-- syr

summary: computes the symmetric rank-1 update of a matrix

inputs:
- N: the number of rows in the matrix
- alpha: the scalar
- X: the vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A

outputs: A with the symmetric rank-1 update
-/
@[extern "leanblas_cblas_dsyr"]
opaque dsyr (order : Order) (uplo : UpLo) (N : USize) (alpha : Float)
    (X : @& FloatArray) (offX incX : USize)
    (A : FloatArray) (offA : USize) (lda : USize) : FloatArray


/-- syr2

summary: computes the symmetric rank-2 update of a matrix

inputs:
- N: the number of rows in the matrix
- alpha: the scalar
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y
- A: the matrix
- offA: starting offset of elements of A
- lda: the leading dimension of A

outputs: A with the symmetric rank-2 update
-/
@[extern "leanblas_cblas_dsyr2"]
opaque dsyr2 (order : Order) (uplo : UpLo) (N : USize) (alpha : Float)
    (X : @& FloatArray) (offX incX : USize)
    (Y : @& FloatArray) (offY incY : USize)
    (A : FloatArray) (offA : USize) (lda : USize) : FloatArray



----------------------------------------------------------------------------------------------------
-- Level 2 BLAS extensions -------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------


/-- dpackedToDense

summary: Converts a packed matrix to a dense matrix

inputs:
- N: the number of rows in the matrix
- uplo: whether the matrix is upper or lower triangular
- orderAp: the order of the packed matrix
- Ap: the packed matrix
- orderA: the order of the dense matrix
- A: the dense matrix
- offA: starting offset of elements of A
- lds: the leading dimension of the dense matrix
-/
@[extern "leanblas_cblas_dpacked_to_dense"]
opaque dpackedToDense (N : USize) (uplo : UpLo)
  (orderAp : Order) (Ap : @& FloatArray)
  (orderA : Order) (A : FloatArray) (offA : USize) (lds : USize) : FloatArray

/-- ddenseToPacked

summary: Converts a dense matrix to a packed matrix

inputs:
- N: the number of rows in the matrix
- uplo: whether the matrix is upper or lower triangular
- orderA: the order of the dense matrix
- A: the dense matrix
- offA: starting offset of elements of A
- lda: the leading dimension of the dense matrix
- orderAp: the order of the packed matrix
- Ap: the packed matrix
-/
@[extern "leanblas_cblas_ddense_to_packed"]
opaque ddenseToPacked (N : USize) (uplo : UpLo)
  (orderA : Order) (A : @& FloatArray) (offA : USize) (lda : USize)
  (orderAp : Order) (Ap : FloatArray) : FloatArray

/-- gpr

summary: General rank-1 update of triangular matrix
  Similar to `ger` but only updates the upper or lower triangle of the matrix

inputs:
- N: the number of rows in the matrix
- alpha: the scalar
- X: the first vector
- offX: starting offset of elements of X
- incX: the increment for the elements of X
- Y: the second vector
- offY: starting offset of elements of Y
- incY: the increment for the elements of Y
- A: triangular matrix in packed format i.e. vector of size N*(N+1)/2
- offA: starting offset of elements of A

outputs: A := A + alpha * X * Y^T
-/
@[extern "leanblas_cblas_dgpr"]
opaque dgpr (order : Order) (uplo : UpLo) (N : USize) (alpha : Float)
    (X : @& FloatArray) (offX incX : USize)
    (Y : @& FloatArray) (offY incY : USize)
    (Ap : FloatArray) (offA : USize) : FloatArray
