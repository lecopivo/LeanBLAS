#include "util.h"
#include <cblas.h>
#include <lean/lean.h>

/** dgemm
 *
 * Computes a general matrix-matrix product.
 * C := alpha*A*B + beta*C
 *
 * @param order Row or column major
 * @param transA No transpose, transpose, or conjugate transpose for A
 * @param transB No transpose, transpose, or conjugate transpose for B
 * @param M Number of rows in matrix C and A (or A^T)
 * @param N Number of columns in matrix C and B (or B^T)
 * @param K Number of columns in A (or A^T) and rows in B (or B^T)
 * @param alpha Scalar multiplier for A*B
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier for C
 * @param C Pointer to matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C with the result of alpha*A*B + beta*C
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
 * C := alpha*A*B + beta*C  or  C := alpha*B*A + beta*C
 *
 * @param order Row or column major
 * @param side Left or right (determines if A is on left or right)
 * @param uplo Upper or lower triangular
 * @param M Number of rows in matrix C
 * @param N Number of columns in matrix C
 * @param alpha Scalar multiplier
 * @param A Pointer to symmetric matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier for C
 * @param C Pointer to matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C with the result
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dsymm(
    const uint8_t order, const uint8_t side, const uint8_t uplo, const size_t M,
    const size_t N, const double alpha, const b_lean_obj_arg A,
    const size_t offA, const size_t lda, const b_lean_obj_arg B,
    const size_t offB, const size_t ldb, const double beta, lean_obj_arg C,
    const size_t offC, const size_t ldc) {
    ensure_exclusive_byte_array(&C);

    cblas_dsymm(leanblas_cblas_order(order), side == 0 ? CblasLeft : CblasRight,
                leanblas_cblas_uplo(uplo), (int)M, (int)N, alpha,
                lean_float_array_cptr(A) + offA, (int)lda,
                lean_float_array_cptr(B) + offB, (int)ldb, beta,
                lean_float_array_cptr(C) + offC, (int)ldc);

    return C;
}

/** dsyrk
 *
 * Performs a symmetric rank-k update.
 * C := alpha*A*A^T + beta*C  or  C := alpha*A^T*A + beta*C
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param trans No transpose or transpose
 * @param N Number of rows and columns in matrix C
 * @param K Number of columns in A (or rows if transposed)
 * @param alpha Scalar multiplier
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param beta Scalar multiplier for C
 * @param C Pointer to symmetric matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C with the result
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
 * C := alpha*A*B^T + alpha*B*A^T + beta*C  or  C := alpha*A^T*B + alpha*B^T*A +
 * beta*C
 *
 * @param order Row or column major
 * @param uplo Upper or lower triangular
 * @param trans No transpose or transpose
 * @param N Number of rows and columns in matrix C
 * @param K Number of columns in A and B (or rows if transposed)
 * @param alpha Scalar multiplier
 * @param A Pointer to matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 * @param beta Scalar multiplier for C
 * @param C Pointer to symmetric matrix C
 * @param offC starting index of C
 * @param ldc Leading dimension of C
 *
 * @return C with the result
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

/** dtrmm
 *
 * Computes a triangular matrix-matrix product.
 * B := alpha*A*B  or  B := alpha*B*A
 *
 * @param order Row or column major
 * @param side Left or right (determines if A is on left or right)
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose for A
 * @param diag Non-unit or unit triangular
 * @param M Number of rows in matrix B
 * @param N Number of columns in matrix B
 * @param alpha Scalar multiplier
 * @param A Pointer to triangular matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 *
 * @return B with the result
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrmm(
    const uint8_t order, const uint8_t side, const uint8_t uplo,
    const uint8_t transA, const uint8_t diag, const size_t M, const size_t N,
    const double alpha, const b_lean_obj_arg A, const size_t offA,
    const size_t lda, lean_obj_arg B, const size_t offB, const size_t ldb) {
    ensure_exclusive_byte_array(&B);

    cblas_dtrmm(leanblas_cblas_order(order), side == 0 ? CblasLeft : CblasRight,
                leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA),
                leanblas_cblas_diag(diag), (int)M, (int)N, alpha,
                lean_float_array_cptr(A) + offA, (int)lda,
                lean_float_array_cptr(B) + offB, (int)ldb);

    return B;
}

/** dtrsm
 *
 * Solves a triangular matrix equation.
 * op(A)*X = alpha*B  or  X*op(A) = alpha*B
 *
 * @param order Row or column major
 * @param side Left or right (determines if A is on left or right)
 * @param uplo Upper or lower triangular
 * @param transA No transpose, transpose, or conjugate transpose for A
 * @param diag Non-unit or unit triangular
 * @param M Number of rows in matrix B
 * @param N Number of columns in matrix B
 * @param alpha Scalar multiplier
 * @param A Pointer to triangular matrix A
 * @param offA starting index of A
 * @param lda Leading dimension of A
 * @param B Pointer to matrix B
 * @param offB starting index of B
 * @param ldb Leading dimension of B
 *
 * @return B with the solution X overwriting B
 */
LEAN_EXPORT lean_obj_res leanblas_cblas_dtrsm(
    const uint8_t order, const uint8_t side, const uint8_t uplo,
    const uint8_t transA, const uint8_t diag, const size_t M, const size_t N,
    const double alpha, const b_lean_obj_arg A, const size_t offA,
    const size_t lda, lean_obj_arg B, const size_t offB, const size_t ldb) {
    ensure_exclusive_byte_array(&B);

    cblas_dtrsm(leanblas_cblas_order(order), side == 0 ? CblasLeft : CblasRight,
                leanblas_cblas_uplo(uplo), leanblas_cblas_transpose(transA),
                leanblas_cblas_diag(diag), (int)M, (int)N, alpha,
                lean_float_array_cptr(A) + offA, (int)lda,
                lean_float_array_cptr(B) + offB, (int)ldb);

    return B;
}