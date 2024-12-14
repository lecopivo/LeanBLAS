#include <lean/lean.h>
#include "cblas.h"


void ensure_exclusive_float_array(lean_obj_arg X){
  if (!lean_is_exclusive(X)) {
    printf("warning: making array copy!\n");
    X = lean_copy_float_array(X);
  }
}

LEAN_EXPORT lean_obj_res leanblas_daxpy(const size_t N, const double alpha, const b_lean_obj_arg X, const size_t incX,
                                  lean_obj_arg Y, const size_t incY){
  ensure_exclusive_float_array(Y);
  cblas_daxpy((int)N, alpha, lean_float_array_cptr(X), (int)incX, lean_float_array_cptr(Y), (int)incY);
  return Y;
}
