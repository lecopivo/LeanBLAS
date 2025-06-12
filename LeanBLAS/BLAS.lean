/-
Copyright (c) 2024 The LeanBLAS Authors. All rights reserved.
Released under the Apache 2.0 license as described in the repository's LICENSE file.
Authors: The LeanBLAS Development Team
-/

import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.CBLAS.LevelTwo

-- Enable missing documentation linter for this file
set_option linter.missingDocs true

open BLAS

/-- 
The main BLAS (Basic Linear Algebra Subprograms) typeclass that provides a unified interface
for linear algebra operations on arrays over a field `K`.

## Type Parameters
- `Array`: The array type that implements BLAS operations
- `R`: The real number type (e.g., `Float` for both real and complex arrays)
- `K`: The field type (can be real like `Float` or complex like `ComplexFloat`)

When `K` is a complex number type, `R` represents the corresponding real number type used
for norms and real-valued operations. When `K` is already real, then `R = K`.

## Examples

For arrays of complex floats:
```lean
instance : BLAS ComplexFloatArray Float ComplexFloat := ...
```

For arrays of real floats:
```lean
instance : BLAS FloatArray Float Float := ...
```

This typeclass extends the level-specific BLAS operations defined in the specification modules.
-/
class BLAS (Array : Type*) (R K : outParam Type*)
  extends
    LevelOneData Array R K,
    LevelOneDataExt Array R K,
    LevelTwoData Array R K
  where

/-- Default BLAS instance for 64-bit floating point arrays.

This provides BLAS operations for arrays of double-precision floating point numbers,
which is the most common use case in scientific computing.
-/
instance : BLAS Float64Array Float Float where


/-- 
A lawful BLAS implementation that satisfies the expected mathematical properties of linear algebra.

## Overview

`LawfulBLAS` represents BLAS implementations where operations satisfy exact mathematical
properties as defined in linear algebra. This is typically true for exact arithmetic
(e.g., rational numbers) but not for floating-point arithmetic due to rounding errors.

## Type Parameters
- `Array`: The array type implementing BLAS operations
- `R`: The real number type with `RCLike` instance
- `K`: The field type with `RCLike` instance
- Requires an existing `BLAS Array R K` instance

## Important Note

For floating-point types, the mathematical laws do not hold exactly due to:
- Rounding errors
- Non-associativity of floating-point addition
- Accumulation of numerical errors

However, we sometimes assume `LawfulBLAS FloatArray Float Float` for the purpose of:
- Source code transformations
- Optimization passes
- Reasoning about algorithm correctness

This typeclass extends the level-specific specifications that define the mathematical
properties each BLAS operation should satisfy.
-/
class LawfulBLAS (Array : Type*) (R K : outParam Type*) [RCLike R] [RCLike K] [BLAS Array R K] : Prop
  extends
    LevelOneSpec Array R K

  where
