

inductive Layout where
  | RowMajor
  | ColMajor

inductive Transpose where
  | NoTrans
  | Trans
  | ConjTrans

inductive UpLo where
  /-- Upper triangular matrix --/
  | Upper
  /-- Lower triangular matrix --/
  | Lower

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
@[extern "leanblas_dgemv"]
opaque dgemv (layout : Layout) (trans : Transpose) (N : USize) (M : USize) (alpha : Float)
    (A : @& FloatArray) (offA : USize) (lda : USize)
    (X : @& FloatArray) (offX incX : USize) (beta : Float)
    (Y : FloatArray) (offY incY : USize) : FloatArray
