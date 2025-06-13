#include <lean/lean.h>
#include <cblas.h>
#include "util.h"


void ensure_exclusive_float_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    /* printf("warning: making array copy!\n"); */
    *X = lean_copy_float_array(*X);
  }
}

void ensure_exclusive_byte_array(lean_object ** X){
  if (!lean_is_exclusive(*X)) {
    /* printf("warning: making array copy!\n"); */
    *X = lean_copy_byte_array(*X);
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

LEAN_EXPORT lean_obj_res leanblas_float_array_to_byte_array(lean_obj_arg a){
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_float_array(a);
  lean_sarray_object * o = lean_to_sarray(r);
  o->m_size *= 8;
  o->m_capacity *= 8;
  lean_set_st_header((lean_object*)o, LeanScalarArray, 1);
  return r;
}

LEAN_EXPORT lean_obj_res leanblas_byte_array_to_float_array(lean_obj_arg a){
  lean_obj_res r;
  if (lean_is_exclusive(a)) r = a;
  else r = lean_copy_byte_array(a);
  lean_sarray_object * o = lean_to_sarray(r);
  o->m_size /= 8;
  o->m_capacity /= 8;
  lean_set_st_header((lean_object*)o, LeanScalarArray, 8);
  return r;
}

LEAN_EXPORT lean_obj_res leanblas_complex_float_array_to_byte_array(lean_obj_arg a){
  // ComplexFloatArray is a wrapper around FloatArray
  // Extract the FloatArray from the ComplexFloatArray structure
  lean_obj_arg float_array = lean_ctor_get(a, 0);
  
  // Convert FloatArray to ByteArray (ComplexFloat64Array)
  lean_obj_res r;
  if (lean_is_exclusive(float_array)) {
    r = float_array;
    lean_inc(r);
  } else {
    r = lean_copy_float_array(float_array);
  }
  
  // Adjust the header to treat as ByteArray
  lean_sarray_object * o = lean_to_sarray(r);
  o->m_size *= 8;
  o->m_capacity *= 8;
  lean_set_st_header((lean_object*)o, LeanScalarArray, 1);
  
  return r;
}

LEAN_EXPORT lean_obj_res leanblas_byte_array_to_complex_float_array(lean_obj_arg a){
  // Convert ByteArray to FloatArray first
  lean_obj_res float_array;
  if (lean_is_exclusive(a)) float_array = a;
  else float_array = lean_copy_byte_array(a);
  
  lean_sarray_object * o = lean_to_sarray(float_array);
  o->m_size /= 8;
  o->m_capacity /= 8;
  lean_set_st_header((lean_object*)o, LeanScalarArray, 8);
  
  // Wrap in ComplexFloatArray constructor
  lean_obj_res r = lean_alloc_ctor(0, 1, 0);
  lean_ctor_set(r, 0, float_array);
  
  return r;
}




