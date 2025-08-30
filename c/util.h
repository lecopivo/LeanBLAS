#include <lean/lean.h>
#include <stdio.h>
#include <cblas.h>


void ensure_exclusive_float_array(lean_object ** X);
void ensure_exclusive_byte_array(lean_object ** X);

CBLAS_ORDER leanblas_cblas_order(const uint8_t order);
CBLAS_TRANSPOSE leanblas_cblas_transpose(const uint8_t trans);
CBLAS_UPLO leanblas_cblas_uplo(const uint8_t uplo);
CBLAS_DIAG leanblas_cblas_diag(const uint8_t diag);
