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
                const blasint N,
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
  ensure_exclusive_float_array(&Ap);

  cblas_dgpr(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), (int)N, alpha,
             lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY,
             lean_float_array_cptr(Ap) + offAp);

  return Ap;
}
