#include "util.h"
#include <cblas.h>
#include <lean/lean.h>

/** dgemm
 *
 * Computes a matrix-matrix product using general matrices.
 *
 * @param order Row or column major
 * @param transA No transpose, transpose, or conjugate transpose for A
 * @param transB No transpose, transpose, or conjugate transpose for B
 * @param M Number of rows in matrices A and C
 * @param N Number of columns in matrices B and C
 * @param K Number of columns in matrix A; number of rows in matrix B
 * @param alpha Scalar multiplier
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier
 * @param C Pointer to matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C with the matrix-matrix product added to it
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dgemm(
    const uint8_t order, const uint8_t transA, const uint8_t transB,
    const size_t M, const size_t N, const size_t K, const double alpha,
    const b_lean_obj_arg A, const size_t offA, const size_t lda,
    const b_lean_obj_arg B, const size_t offB, const size_t ldb,
    const double beta, lean_obj_arg C, const size_t offC, const size_t ldc) {
  ensure_exclusive_byte_array(&C);

  cblas_dgemm(leanblas_cblas_order(order), leanblas_cblas_transpose(transA),
              leanblas_cblas_transpose(transB), (int)M, (int)N, (int)K, alpha,
              lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(B) + offB, (int)ldb, beta,
              lean_float_array_cptr(C) + offC, (int)ldc);

  return C;
}

/** dsymm
 *
 * Computes a matrix-matrix product where one matrix is symmetric.
 *
 * @param order Row or column major
 * @param side Side on which the symmetric matrix A is multiplied (Left or
 * Right)
 * @param uplo Upper or lower triangular part of A is used
 * @param M Number of rows in matrix C
 * @param N Number of columns in matrix C
 * @param alpha Scalar multiplier
 * @param A Pointer to symmetric matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to general matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier
 * @param C Pointer to general matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C updated
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsymm(
    const uint8_t order, const uint8_t side, const uint8_t uplo, const size_t M,
    const size_t N, const double alpha, const b_lean_obj_arg A,
    const size_t offA, const size_t lda, const b_lean_obj_arg B,
    const size_t offB, const size_t ldb, const double beta, lean_obj_arg C,
    const size_t offC, const size_t ldc) {
  ensure_exclusive_byte_array(&C);

  cblas_dsymm(leanblas_cblas_order(order), leanblas_cblas_side(side),
              leanblas_cblas_uplo(uplo), (int)M, (int)N, alpha,
              lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(B) + offB, (int)ldb, beta,
              lean_float_array_cptr(C) + offC, (int)ldc);

  return C;
}

/** dtrmm
 *
 * Computes a matrix-matrix product where one matrix is triangular.
 *
 * @param order Row or column major
 * @param side Side on which the triangular matrix A is multiplied (Left or
 * Right)
 * @param uplo Upper or lower triangular part of A is used
 * @param transA No transpose or transpose for A
 * @param diag Unit or non-unit triangular
 * @param M Number of rows in matrix B
 * @param N Number of columns in matrix B
 * @param alpha Scalar multiplier
 * @param A Pointer to triangular matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to general matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 *
 * @return Updated B
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrmm(
    const uint8_t order, const uint8_t side, const uint8_t uplo,
    const uint8_t transA, const uint8_t diag, const size_t M, const size_t N,
    const double alpha, const b_lean_obj_arg A, const size_t offA,
    const size_t lda, lean_obj_arg B, const size_t offB, const size_t ldb) {
  ensure_exclusive_byte_array(&B);

  cblas_dtrmm(leanblas_cblas_order(order), leanblas_cblas_side(side),
              leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA),
              leanblas_cblas_diag(diag), (int)M, (int)N, alpha,
              lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(B) + offB, (int)ldb);

  return B;
}

/** dtrsm
 *
 * Solves a matrix equation with a triangular matrix.
 *
 * @param order Row or column major
 * @param side Side on which the triangular matrix A is multiplied (Left or
 * Right)
 * @param uplo Upper or lower triangular part of A is used
 * @param transA No transpose or transpose for A
 * @param diag Unit or non-unit triangular
 * @param M Number of rows in matrix B
 * @param N Number of columns in matrix B
 * @param alpha Scalar multiplier
 * @param A Pointer to triangular matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to general matrix B (right-hand side and result)
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 *
 * @return B replaced by the solution X
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrsm(
    const uint8_t order, const uint8_t side, const uint8_t uplo,
    const uint8_t transA, const uint8_t diag, const size_t M, const size_t N,
    const double alpha, const b_lean_obj_arg A, const size_t offA,
    const size_t lda, lean_obj_arg B, const size_t offB, const size_t ldb) {
  ensure_exclusive_byte_array(&B);

  cblas_dtrsm(leanblas_cblas_order(order), leanblas_cblas_side(side),
              leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA),
              leanblas_cblas_diag(diag), (int)M, (int)N, alpha,
              lean_float_array_cptr(A) + offA, (int)lda,
              lean_float_array_cptr(B) + offB, (int)ldb);

  return B;
}

/** dsyrk
 *
 * Performs a symmetric rank-k update.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangle of C is updated
 * @param trans No transpose (A*A^T) or transpose (A^T*A)
 * @param N Order of matrix C
 * @param K Number of columns of A (if trans=NoTrans) or rows of A (if
 * trans=Trans)
 * @param alpha Scalar multiplier
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param beta Scalar multiplier
 * @param C Pointer to symmetric matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return Updated C
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsyrk(
    const uint8_t order, const uint8_t uplo, const uint8_t trans,
    const size_t N, const size_t K, const double alpha, const b_lean_obj_arg A,
    const size_t offA, const size_t lda, const double beta, lean_obj_arg C,
    const size_t offC, const size_t ldc) {
  ensure_exclusive_byte_array(&C);

  cblas_dsyrk(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo),
              leanblas_cblas_transpose(trans), (int)N, (int)K, alpha,
              lean_float_array_cptr(A) + offA, (int)lda, beta,
              lean_float_array_cptr(C) + offC, (int)ldc);

  return C;
}

/** dsyr2k
 *
 * Performs a symmetric rank-2k update.
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangle of C is updated
 * @param trans No transpose or transpose
 * @param N Order of matrix C
 * @param K Number of columns of A/B (if trans=NoTrans) or rows of A/B (if
 * trans=Trans)
 * @param alpha Scalar multiplier
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier
 * @param C Pointer to symmetric matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return Updated C
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsyr2k(
    const uint8_t order, const uint8_t uplo, const uint8_t trans,
    const size_t N, const size_t K, const double alpha, const b_lean_obj_arg A,
    const size_t offA, const size_t lda, const b_lean_obj_arg B,
    const size_t offB, const size_t ldb, const double beta, lean_obj_arg C,
    const size_t offC, const size_t ldc) {
  ensure_exclusive_byte_array(&C);

  cblas_dsyr2k(leanblas_cblas_order(order), leanblas_cblas_uplo(uplo),
               leanblas_cblas_transpose(trans), (int)N, (int)K, alpha,
               lean_float_array_cptr(A) + offA, (int)lda,
               lean_float_array_cptr(B) + offB, (int)ldb, beta,
               lean_float_array_cptr(C) + offC, (int)ldc);

  return C;
}
