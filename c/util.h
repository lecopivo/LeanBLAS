#include <lean/lean.h>
#include <cblas.h>


void ensure_exclusive_float_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    /* printf("warning: making array copy!\n"); */
    *X = lean_copy_float_array(*X);
  }
}


CBLAS_ORDER leanblas_cblas_order(const uint8_t order) {
  if (order == 0) {
    return CblasRowMajor;
  } else {
    return CblasColMajor;
  }
}

CBLAS_TRANSPOSE leanblas_cblas_transpose(const uint8_t trans) {
  switch (trans) {
    case 0:
      return CblasNoTrans;
    case 1:
      return CblasTrans;
    case 2:
      return CblasConjTrans;
    case 3:
      return CblasConjNoTrans;
    default:
      return CblasNoTrans;
  }
}

CBLAS_UPLO leanblas_cblas_uplo(const uint8_t uplo) {
  switch (uplo) {
    case 0:
      return CblasUpper;
    case 1:
      return CblasLower;
    default:
      return CblasUpper;
  }
}

CBLAS_DIAG leanblas_cblas_diag(const uint8_t diag) {
  switch (diag) {
    case 0:
      return CblasNonUnit;
    case 1:
      return CblasUnit;
    default:
      return CblasNonUnit;
  }
}
