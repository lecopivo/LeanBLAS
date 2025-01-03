#include <lean/lean.h>
#include <cblas.h>
#include "util.h"


/** dgemv
 *
 * Computes a matrix-vector product using a general matrix.

  * @param order Row or column major
  * @param transA No transpose, transpose, or conjugate transpose
  * @param M Number of rows in matrix
  * @param N Number of columns in matrix
  * @param alpha Scalar multiplier
  * @param A Pointer to input matrix
  * @param offA starting index of A
  * @param lda Leading dimension of A
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param beta Scalar multiplier
  * @param Y Pointer to output vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  *
  * @return Y with the matrix-vector product added to it
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dgemv(const uint8_t order, const uint8_t transA,
                                const size_t M, const size_t N, const double alpha,
                                const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                const double beta, lean_obj_arg Y, const size_t offY, const size_t incY){
  ensure_exclusive_float_array(&Y);

  cblas_dgemv(leanblas_cblas_order(order), leanblas_cblas_transpose(transA),
              (int)M, (int)N, alpha, lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(X) + offX, (int)incX, beta, lean_float_array_cptr(Y) + offY, (int)incY);

  return Y;
}



/** dgbmv
  *
  * Computes a matrix-vector product using a general band matrix.
  
    * @param order Row or column
    * @param transA No transpose, transpose, or conjugate transpose
    * @param M Number of rows in matrix
    * @param N Number of columns in matrix
    * @param KL Number of sub-diagonals in matrix
    * @param KU Number of super-diagonals in matrix
    * @param alpha Scalar multiplier
    * @param A Pointer to input matrix
    * @param offA starting index of A
    * @param lda Leading dimension of A
    * @param X Pointer to input vector
    * @param offX starting index of X
    * @param incX Increment for the elements of X
    * @param beta Scalar multiplier
    * @param Y Pointer to output vector
    * @param offY starting index of Y
    * @param incY Increment for the elements of Y
    *
    * @return Y with the matrix-vector product added to it
    */
LEAN_EXPORT lean_obj_res leanblas_cblas_dgbmv(const uint8_t order, const uint8_t transA,
                                const size_t M, const size_t N, const size_t KL, const size_t KU, const double alpha,
                                const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                const double beta, lean_obj_arg Y, const size_t offY, const size_t incY){
  ensure_exclusive_float_array(&Y);

  cblas_dgbmv(leanblas_cblas_order(order), leanblas_cblas_transpose(transA),
              (int)M, (int)N, (int)KL, (int)KU, alpha, lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(X) + offX, (int)incX, beta, lean_float_array_cptr(Y) + offY, (int)incY);

  return Y;
}



/** dtrmv
 *
 * Computes a matrix-vector product using a triangular matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param A Pointer to input matrix
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the matrix-vector product added to it
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrmv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtrmv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, lean_float_array_cptr(A) + offA, (int)lda, lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** dtbmv
 *
 * Computes a matrix-vector product using a triangular band matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param K Number of super-diagonals in matrix
 * @param A Pointer to input matrix
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the matrix-vector product added to it
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtbmv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const size_t K, const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtbmv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, (int)K, lean_float_array_cptr(A) + offA, (int)lda, lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** dtpmv
 *
 * Computes a matrix-vector product using a triangular packed matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param A Pointer to input matrix
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the matrix-vector product added to it
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtpmv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const b_lean_obj_arg A, lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtpmv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, lean_float_array_cptr(A), lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** dtrsv
 *
 * Solves a system of linear equations with a triangular matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param A Pointer to input matrix
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the solution to the system of linear equations
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrsv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtrsv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, lean_float_array_cptr(A) + offA, (int)lda, lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** dtbsv
 *
 * Solves a system of linear equations with a triangular band matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param K Number of super-diagonals in matrix
 * @param A Pointer to input matrix
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the solution to the system of linear equations
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtbsv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const size_t K, const b_lean_obj_arg A, const size_t offA, const size_t lda,
                                lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtbsv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, (int)K, lean_float_array_cptr(A) + offA, (int)lda, lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** dtpsv
 *
 * Solves a system of linear equations with a triangular packed matrix.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose
 * @param diag Non-unit or unit triangular
 * @param N Number of rows in matrix
 * @param A Pointer to input matrix
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return X with the solution to the system of linear equations
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtpsv(const uint8_t order, const uint8_t uplo, const uint8_t transA, const uint8_t diag,
                                const size_t N, const b_lean_obj_arg A, lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);

  cblas_dtpsv(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA), leanblas_cblas_diag(diag),
              (int)N, lean_float_array_cptr(A), lean_float_array_cptr(X) + offX, (int)incX);

  return X;
}


/** ger
 *
 * Computes the outer product of two vectors.
 *
 * @param order Row or column major
 * @param M Number of rows in matrix
 * @param N Number of columns in matrix
 * @param alpha Scalar multiplier
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 * @param Y Pointer to input vector
 * @param offY starting index of Y
 * @param incY Increment for the elements of Y
 * @param A Pointer to output matrix
 * @param offA starting index of A
 * @param lda Leading dimension of A
 *
 * @return A with the outer product added to it
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dger(const uint8_t order, const size_t M, const size_t N, const double alpha,
                                const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                const b_lean_obj_arg Y, const size_t offY, const size_t incY,
                                lean_obj_arg A, const size_t offA, const size_t lda){
  ensure_exclusive_float_array(&A);

  cblas_dger(leanblas_cblas_order(order), (int)M, (int)N, alpha,
             lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY,
             lean_float_array_cptr(A) + offA, (int)lda);

  return A;
}



/** syr
  *
  * Computes the outer product of a vector with itself and adds it to a symmetric matrix.
  *
  * @param order Row or column major
  * @param uplo Upper or lower triangular
  * @param N Number of rows in matrix
  * @param alpha Scalar multiplier
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param A Pointer to output matrix
  * @param offA starting index of A
  * @param lda Leading dimension of A
  *
  * @return A with the outer product added to it
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsyr(const uint8_t order, const uint8_t uplo,
                              const size_t N, const double alpha,
                              const b_lean_obj_arg X, const size_t offX, const size_t incX,
                              lean_obj_arg A, const size_t offA, const size_t lda){
  ensure_exclusive_float_array(&A);

  cblas_dsyr(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo),
             (int)N, alpha, lean_float_array_cptr(X) + offX, (int)incX,
             lean_float_array_cptr(A) + offA, (int)lda);

  return A;
}


/** syr2
  *
  * Computes the outer product of two vectors and adds it to a symmetric matrix.
  *
  * @param order Row or column major
  * @param uplo Upper or lower triangular
  * @param N Number of rows in matrix
  * @param alpha Scalar multiplier
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to input vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  * @param A Pointer to output matrix
  * @param offA starting index of A
  * @param lda Leading dimension of A
  *
  * @return A with the outer product added to it
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsyr2(const uint8_t order, const uint8_t uplo,
                               const size_t N, const double alpha,
                               const b_lean_obj_arg X, const size_t offX, const size_t incX,
                               const b_lean_obj_arg Y, const size_t offY, const size_t incY,
                               lean_obj_arg A, const size_t offA, const size_t lda){
  ensure_exclusive_float_array(&A);

  cblas_dsyr2(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo),
              (int)N, alpha, lean_float_array_cptr(X) + offX, (int)incX,
              lean_float_array_cptr(Y) + offY, (int)incY,
              lean_float_array_cptr(A) + offA, (int)lda);

  return A;
}
