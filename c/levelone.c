#include <lean/lean.h>
#include <cblas.h>
#include "util.h"


/** ddot
 *
 * Computes the dot product of two vectors.
 *
 * @param N Number of elements in input vectors
 * @param X Pointer to first input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 * @param Y Pointer to second input vector
 * @param offY starting index of Y
 * @param incY Increment for the elements of Y
 *
 * @return Dot product of X and Y
 */
LEAN_EXPORT double leanblas_cblas_ddot(const size_t N,
                                 const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                 const b_lean_obj_arg Y, const size_t offY, const size_t incY){
  return cblas_ddot((int)N, lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY);
}



/** zdot
 *
  * Computes the dot product of two complex vectors.
  *
  * @param N Number of elements in input vectors
  * @param X Pointer to first input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to second input vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  *
  * @return Dot product of X and Y
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_zdot(const size_t N,
                                       const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                       const b_lean_obj_arg Y, const size_t offY, const size_t incY){

  double r[2];
  cblas_zdotc_sub((int)N, (void *)(lean_float_array_cptr(X) + 2*offX), (int)incX,
                          (void *)(lean_float_array_cptr(Y) + 2*offY), (int)incY, r);

  lean_obj_res lean_res = lean_alloc_ctor(0, 0, 2*sizeof(double));
  lean_ctor_set_float(lean_res, 0*sizeof(double), r[0]);
  lean_ctor_set_float(lean_res, 1*sizeof(double), r[1]);
  return lean_res;
}




/** dnrm2
 *
 * Computes the Euclidean norm of a vector.
 *
 * @param N Number of elements in input vector
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return Euclidean norm of X
 */
LEAN_EXPORT double leanblas_cblas_dnrm2(const size_t N, const b_lean_obj_arg X, const size_t offX, const size_t incX){
  return cblas_dnrm2((int)N, lean_float_array_cptr(X) + offX, (int)incX);
}


/** dasum
 *
 * Computes the sum of the absolute values of the elements of a vector.
 *
 * @param N Number of elements in input vector
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return Sum of the absolute values of the elements of X
 */
LEAN_EXPORT double leanblas_cblas_dasum(const size_t N, const b_lean_obj_arg X, const size_t offX, const size_t incX){
  return cblas_dasum((int)N, lean_float_array_cptr(X) + offX, (int)incX);
}

/** idamax
 *
 * Finds the index of the first element with maximum absolute value.
 *
 * @param N Number of elements in input vector
 * @param X Pointer to input vector
 * @param offX starting index of X
 * @param incX Increment for the elements of X
 *
 * @return Index of the first element with maximum absolute value
 */
LEAN_EXPORT size_t leanblas_cblas_idamax(const size_t N, const b_lean_obj_arg X, const size_t offX, const size_t incX){
  return cblas_idamax((int)N, lean_float_array_cptr(X) + offX, (int)incX);
}


/** dswap
  *
  * Interchanges two vectors.
  *
  * @param N Number of elements in input vectors
  * @param X Pointer to first input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to second input vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y

  * @return X and Y with their elements interchanged
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dswap(const size_t N, lean_obj_arg X, const size_t offX, const size_t incX,
                                lean_obj_arg Y, const size_t offY, const size_t incY){
  ensure_exclusive_float_array(&X);
  ensure_exclusive_float_array(&Y);
  cblas_dswap((int)N, lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY);

  lean_obj_res res = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(res, 0, X);
  lean_ctor_set(res, 1, Y);
  return res;
}


/** dcopy
  *
  * Copies a vector, X, to a vector, Y.
  *
  * @param N Number of elements in input vectors
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to output vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  *
  * @return Y with the elements of X copied to it
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dcopy(const size_t N, const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                lean_obj_arg Y, const size_t offY, const size_t incY){
  ensure_exclusive_float_array(&Y);
  cblas_dcopy((int)N, lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY);
  return Y;
}

/** daxpy
  *
  * Computes a vector, Y, plus a scalar multiple of a vector, X.
  *
  * @param N Number of elements in input vectors
  * @param alpha Scalar multiplier
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to output vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  *
  * @return Y with the elements of alpha*X added to it
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_daxpy(const size_t N, const double alpha, const b_lean_obj_arg X, const size_t offX, const size_t incX,
                                lean_obj_arg Y, const size_t offY, const size_t incY){
  ensure_exclusive_float_array(&Y);
  cblas_daxpy((int)N, alpha, lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY);
  return Y;
}
 


/** drotg
  *
  * Constructs a Givens plane rotation.
  *
  * @param a First input scalar
  * @param b Second input scalar
  * @param c Cosine of the angle of rotation
  * @param s Sine of the angle of rotation
  *
  * @return a, b, c, and s with the Givens plane rotation constructed
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_drotg(double a, double b){
  double c, s;
  cblas_drotg(&a, &b, &c, &s);

  lean_obj_res res = lean_alloc_ctor(0, 4, 0);
  lean_ctor_set(res, 0, lean_box(a));
  lean_ctor_set(res, 1, lean_box(b));
  lean_ctor_set(res, 2, lean_box(c));
  lean_ctor_set(res, 3, lean_box(s));
  return res;
}


/** drotmg
  *
  * Constructs a modified Givens plane rotation.
  *
  * @param d1 First input scalar
  * @param d2 Second input scalar
  * @param x1 First input vector
  * @param y1 Second input vector
  * @param param Pointer to output vector
  *
  * @return d1, d2, x1, y1, and param with the modified Givens plane rotation constructed
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_drotmg(const double d1, const double d2, const double x1, const double y1){
  double d1_out, d2_out, x1_out, y1_out;
  double param[5];
  cblas_drotmg(&d1_out, &d2_out, &x1_out, y1_out, param);

  printf("fix implementation of drotmg\n");

  lean_obj_res res = lean_alloc_ctor(0, 5, 0);
  lean_ctor_set(res, 0, lean_box(d1_out));
  lean_ctor_set(res, 1, lean_box(d2_out));
  lean_ctor_set(res, 2, lean_box(x1_out));
  lean_ctor_set(res, 3, lean_box(y1_out));
  lean_ctor_set(res, 4, lean_box(0));
  return res;
}


/** drot
  *
  * Applies a Givens plane rotation to a pair of vectors.
  *
  * @param N Number of elements in input vectors
  * @param X Pointer to first input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  * @param Y Pointer to second input vector
  * @param offY starting index of Y
  * @param incY Increment for the elements of Y
  * @param c Cosine of the angle of rotation
  * @param s Sine of the angle of rotation
  *
  * @return X and Y with the Givens plane rotation applied
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_drot(const size_t N, lean_obj_arg X, const size_t offX, const size_t incX,
                               lean_obj_arg Y, const size_t offY, const size_t incY, const double c, const double s){
  ensure_exclusive_float_array(&X);
  ensure_exclusive_float_array(&Y);
  cblas_drot((int)N, lean_float_array_cptr(X) + offX, (int)incX, lean_float_array_cptr(Y) + offY, (int)incY, c, s);

  lean_obj_res res = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(res, 0, X);
  lean_ctor_set(res, 1, Y);
  return res;
}
 

/** dscal
  *
  * Scales a vector by a constant.
  *
  * @param N Number of elements in input vector
  * @param alpha Scalar multiplier
  * @param X Pointer to input vector
  * @param offX starting index of X
  * @param incX Increment for the elements of X
  *
  * @return X with the elements scaled by alpha
  */
LEAN_EXPORT lean_obj_res leanblas_cblas_dscal(const size_t N, const double alpha, lean_obj_arg X, const size_t offX, const size_t incX){
  ensure_exclusive_float_array(&X);
  cblas_dscal((int)N, alpha, lean_float_array_cptr(X) + offX, (int)incX);
  return X;
}
