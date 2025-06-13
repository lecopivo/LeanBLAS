-- import LeanBLAS.CBLAS.LevelOneFloat32
-- import LeanBLAS.CBLAS.LevelOneComplexFloat32
import LeanBLAS.FFI.CBLASLevelOneFloat64
import LeanBLAS.Spec.LevelOne

/-!
# CBLAS Level 1 Implementation

This module provides the CBLAS (C interface to BLAS) implementation of Level 1 BLAS operations
for Float64Array types. Level 1 operations are vector-vector operations with O(n) complexity.

## Overview

The implementation uses FFI (Foreign Function Interface) bindings to call optimized BLAS
libraries (OpenBLAS, MKL, or system BLAS) for actual computation. This ensures:
- High performance through optimized machine code
- Compatibility with existing BLAS ecosystem
- Validated numerical algorithms

## Implementation Details

All operations map Lean's natural numbers to C's size_t/int types and handle the conversion
between Lean arrays and C arrays through the FFI layer. The `sorry_proof` placeholders are
used for array bounds checking proofs that will be formalized in future work.

## Available Operations

- Vector dot products: `dot`
- Euclidean norm: `nrm2`
- Sum of absolute values: `asum`
- Index of maximum absolute value: `iamax`
- Vector operations: `swap`, `copy`, `axpy`, `scal`
- Givens rotations: `rotg`, `rotmg`, `rot`
-/

namespace BLAS.CBLAS

open Sorry

/-- CBLAS implementation of Level 1 BLAS operations for Float64Array.
    
This instance provides efficient implementations of vector operations by calling
optimized BLAS libraries through FFI. All index parameters (offsets and strides)
are converted from Nat to USize for C compatibility. -/
instance : LevelOneData Float64Array Float Float where
  size x := x.size
  get x i := (cast sorry_proof x : FloatArray).uget i.toUSize sorry_proof
  dot N X offX incX Y offY incY := ddot N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  nrm2 N X offX incX := dnrm2 N.toUSize X offX.toUSize incX.toUSize
  asum N X offX incX := dasum N.toUSize X offX.toUSize incX.toUSize
  iamax N X offX incX := idamax N.toUSize X offX.toUSize incX.toUSize |>.toNat
  swap N X offX incX Y offY incY := dswap N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  copy N X offX incX Y offY incY := dcopy N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  axpy N a X offX incX Y offY incY := daxpy N.toUSize a X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  rotg a b := drotg a b
  rotmg d1 d2 b1 b2 := drotmg d1 d2 b1 b2
  rot N X offX incX Y offY incY c s := drot N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize c s
  scal N a X offX incX := dscal N.toUSize a X offX.toUSize incX.toUSize



set_option linter.unusedVariables false in
instance : LevelOneDataExt Float64Array Float Float where
  const N a := dconst N.toUSize a
  sum N X offX incX := dsum N.toUSize X offX.toUSize incX.toUSize
  axpby N a X offX incX b Y offY incY := daxpby N.toUSize a X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize
  scaladd N a X offX incX b := dscaladd N.toUSize a X offX.toUSize incX.toUSize b

  imaxRe N X offX incX h := (dimaxRe N.toUSize X offX.toUSize incX.toUSize).toNat
  imaxIm N X offX incX h := offX
  iminRe N X offX incX h := (diminRe N.toUSize X offX.toUSize incX.toUSize).toNat
  iminIm N X offX incX h := offX

  mul N X offX incX Y offY incY := dmul N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  div N X offX incX Y offY incY := ddiv N.toUSize X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize
  inv N X offX incX := dinv N.toUSize X offX.toUSize incX.toUSize
  abs N X offX incX := dabs N.toUSize X offX.toUSize incX.toUSize
  sqrt N X offX incX := dsqrt N.toUSize X offX.toUSize incX.toUSize
  exp N X offX incX := dexp N.toUSize X offX.toUSize incX.toUSize
  log N X offX incX := dlog N.toUSize X offX.toUSize incX.toUSize
  sin N X offX incX := dsin N.toUSize X offX.toUSize incX.toUSize
  cos N X offX incX := dcos N.toUSize X offX.toUSize incX.toUSize
