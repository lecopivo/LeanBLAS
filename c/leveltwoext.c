#include <lean/lean.h>
#include <cblas.h>
#include "util.h"


/** General packed rank-1 update
 *
 * Similar to `ger` but for packed triangular matrices. Standard `ger` operation might lead not
 * matrix that is no longer triangular but this operation just ignores the corresponding elements
 * above or bellow the main diagonal.
 *
 * A := alpha * m(x * y^T) + A
 *
 * where `m` sets all element to zero above or below the main diagonal
 */
void cblas_dgpr(const enum CBLAS_ORDER order,
                const enum CBLAS_UPLO Uplo,
                const int N,
                const double alpha,
                const double *X, int incX,
                const double *Y, int incY,
                double *Ap){

  if (order == CblasColMajor && Uplo == CblasLower){

    int idx = 0;
    for (int j=0; j<N; j++){
      const double yj = Y[j*incY];

      if (yj == 0.0){
        idx += N-j;
        continue;
      }

      for (int i=j; i<N; i++){
        const double xi = X[i*incX];
        Ap[idx] += alpha * xi * yj;
        idx++;
      }
    }
  } else if (order == CblasColMajor && Uplo == CblasUpper){

    int idx = 0;
    for (int j=0; j<N; j++){
      const double yj = Y[j*incY];

      if (yj == 0.0){
        idx += j+1;
        continue;
      }

      for (int i=0; i<=j; i++){
        const double xi = X[i*incX];
        Ap[idx] += alpha * xi * yj;
        idx++;
      }
    }
  } else if (order == CblasRowMajor && Uplo == CblasLower){

    int idx = 0;
    for (int i=0; i<N; i++){
      const double xi = X[i*incX];

      if (xi == 0.0){
        idx += i+1;
        continue;
      }

      for (int j=0; j<=i; j++){
        const double yj = Y[j*incY];
        Ap[idx] += alpha * xi * yj;
        idx++;
      }
    }
  } else if (order == CblasRowMajor && Uplo == CblasUpper){

    int idx = 0;
    for (int i=0; i<N; i++){
      const double xi = X[i*incX];

      if (xi == 0.0){
        idx += N-i;
        continue;
      }

      for (int j=i; j<N; j++){
        const double yj = Y[j*incY];
        Ap[idx] += alpha * xi * yj;
        idx++;
      }
    }
  }
}


/** General packed rank-1 update

 * Similar to `ger` but for packed triangular matrices. Standard `ger` operation might lead not
 * matrix that is no longer triangular but this operation just ignores the corresponding elements
 * above or bellow the main diagonal.
 *
 * A := alpha * m(x * y^T) + A
 *
 * where `m` sets all element to zero above or below the main diagonal
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dgpr(const uint8_t order, const uint8_t uplo,
                                const size_t N, const double alpha,
                                const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                const b_lean_obj_arg Y, const size_t offY, const size_t incY,
                                lean_obj_arg Ap, const size_t offAp){
  ensure_exclusive_byte_array(&Ap);

  cblas_dgpr(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), (int)N, alpha,
             lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY,
             lean_float_array_cptr(Ap) + offAp);

  return Ap;
}


/** Convert packed matrix to dense matrix
 * It zeros out the elements above or below the main diagonal based on the `uplo` parameter.
 */
void cblas_dpacked_to_dense(const int N,
                           const enum CBLAS_UPLO uplo,
                           const enum CBLAS_ORDER orderX,
                           const double *X,
                           const enum CBLAS_ORDER orderA,
                           double *A, const int lda){

  // The order of X dictates the order of for loops.
  // This makes the implementation easier, but ordering loops based on the order of A might be faster
  // due to better memory access patterns and cache utilization.
  // it makes implementation easier, ordering loops based on order of A might be faster
  if (uplo == CblasLower && orderX == CblasColMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<j; i++){
        A[i+j*lda] = 0;
      }
      for (int i=j; i<N; i++){
        A[i+j*lda] = X[idx];
        idx++;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasColMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<j; i++){
        A[j+i*lda] = 0;
      }
      for (int i=j; i<N; i++){
        A[j+i*lda] = X[idx];
        idx++;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasRowMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<=i; j++){
        A[i+j*lda] = X[idx];
        idx++;
      }
      for (int j=i+1; j<N; j++){
        A[i+j*lda] = 0;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasRowMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<=i; j++){
        A[j+i*lda] = X[idx];
        idx++;
      }
      for (int j=i+1; j<N; j++){
        A[j+i*lda] = 0;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasColMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<=j; i++){
        A[i+j*lda] = X[idx];
        idx++;
      }
      for (int i=j+1; i<N; i++){
        A[i+j*lda] = 0;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasColMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<=j; i++){
        A[j+i*lda] = X[idx];
        idx++;
      }
      for (int i=j+1; i<N; i++){
        A[j+i*lda] = 0;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasRowMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<i; j++){
        A[i+j*lda] = 0;
      }
      for (int j=i; j<N; j++){
        A[i+j*lda] = X[idx];
        idx++;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasRowMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<i; j++){
        A[j+i*lda] = 0;
      }
      for (int j=i; j<N; j++){
        A[j+i*lda] = X[idx];
        idx++;
      }
    }
  }
}

LEAN_EXPORT lean_obj_res leanblas_cblas_dpacked_to_dense(const size_t N,
                                                        const uint8_t uplo,
                                                        const uint8_t orderAp,
                                                        const b_lean_obj_arg Ap,
                                                        const uint8_t orderA,
                                                        lean_obj_arg A,
                                                        const size_t offA,
                                                        const size_t lda){

  ensure_exclusive_byte_array(&A);

  cblas_dpacked_to_dense((int)N, leanblas_cblas_uplo(uplo),
                         leanblas_cblas_order(orderAp), lean_float_array_cptr(Ap),
                         leanblas_cblas_order(orderA),  lean_float_array_cptr(A) + offA, (int)lda);

  return A;
}


/** Extract lower/upper triangular part of dense matrix `A` and stores it in packed format. */
/**
 * Extracts the lower or upper triangular part of a dense matrix `A` and stores it in packed format.
 *
 * @param N The order of the matrix `A`.
 * @param orderA The storage order of the matrix `A` (row-major or column-major).
 * @param A The input dense matrix.
 * @param lda The leading dimension of the matrix `A`.
  // The order of X dictates the order of the for loops. While this makes the implementation easier, ordering loops based on the order of A might be faster due to better memory access patterns and cache utilization.
 * @param orderX The storage order of the packed matrix `X` (row-major or column-major).
 * @param X The output packed matrix.
 */
void cblas_ddense_to_packed(const int N,
                            const enum CBLAS_UPLO uplo,
                            const enum CBLAS_ORDER orderA,
                            const double *A, const int lda,
                            const enum CBLAS_ORDER orderX,
                            double *X){

  // order of X dictates the order of for loops
  // it makes implementation easier, ordering loops based on order of A might be faster
  if (uplo == CblasLower && orderX == CblasColMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=j; i<N; i++){
        X[idx] = A[i+j*lda];
        idx++;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasColMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=j; i<N; i++){
        X[idx] = A[j+i*lda];
        idx++;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasRowMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<=i; j++){
        X[idx] = A[i+j*lda];
        idx++;
      }
    }
  } else if (uplo == CblasLower && orderX == CblasRowMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=0; j<=i; j++){
        X[idx] = A[j+i*lda];
        idx++;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasColMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<=j; i++){
        X[idx] = A[i+j*lda];
        idx++;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasColMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int j=0; j<N; j++){
      for (int i=0; i<=j; i++){
        X[idx] = A[j+i*lda];
        idx++;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasRowMajor && orderA == CblasColMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=i; j<N; j++){
        X[idx] = A[i+j*lda];
        idx++;
      }
    }
  } else if (uplo == CblasUpper && orderX == CblasRowMajor && orderA == CblasRowMajor){
    int idx = 0;
    for (int i=0; i<N; i++){
      for (int j=i; j<N; j++){
        X[idx] = A[j+i*lda];
        idx++;
      }
    }
  }
}

/** Extract lower/upper triangular part of dense matrix `A` and stores it in packed format. */
LEAN_EXPORT lean_obj_res leanblas_cblas_ddense_to_packed(const size_t N,
                                                         const uint8_t uplo,
                                                         const uint8_t orderA,
                                                         const b_lean_obj_arg A,
                                                         const size_t offA,
                                                         const size_t lda,
                                                         const uint8_t orderAp,
                                                         lean_obj_arg Ap){

  ensure_exclusive_byte_array(&Ap);

  cblas_ddense_to_packed((int)N, leanblas_cblas_uplo(uplo),
                         leanblas_cblas_order(orderA),  lean_float_array_cptr(A) + offA, (int)lda,
                         leanblas_cblas_order(orderAp), lean_float_array_cptr(Ap));

  return Ap;
}
