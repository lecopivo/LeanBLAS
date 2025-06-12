/-
Copyright (c) 2024 The LeanBLAS Authors. All rights reserved.
Released under the Apache 2.0 license as described in the repository's LICENSE file.
Authors: The LeanBLAS Development Team
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic

import LeanBLAS.Util

-- Enable missing documentation linter for this file
set_option linter.missingDocs true

/-!
## Scalar Type Conversions

This module provides conversion functions between different scalar types used in BLAS operations.

BLAS operations work with both real and complex numbers, and this module provides a uniform
interface for converting between them through the `RCLike` typeclass from Mathlib.
-/

namespace BLAS

open Sorry RCLike

/-- Local notation for the algebra map from real numbers to an arbitrary `RCLike` type. -/
local notation "𝓚" => algebraMap ℝ _

/-- 
Extract the real part of a scalar value.

For real numbers, this is the identity function.
For complex numbers, this extracts the real component.

## Example
```lean
example : toReal (5 : ℝ) = 5 := rfl
example : toReal ((3 : ℂ) + 4*I) = 3 := by simp [toReal]
```
-/
noncomputable
def toReal {𝕜} [RCLike 𝕜] (x : 𝕜) : ℝ := re x

/--
Convert a real number to a scalar type `𝕜`.

This uses the algebra map to embed real numbers into the target type.
For `𝕜 = ℝ`, this is the identity.
For `𝕜 = ℂ`, this creates a complex number with zero imaginary part.

## Example
```lean
example : fromReal ℝ 5 = 5 := by simp [fromReal]
example : fromReal ℂ 5 = (5 : ℂ) := by simp [fromReal]
```
-/
noncomputable
def fromReal (𝕜 : Type*) [RCLike 𝕜] (x : ℝ) : 𝕜 := 𝓚 x

/--
Convert a scalar value to a complex number.

Extracts both real and imaginary parts to construct a complex number.
For real inputs, the imaginary part is zero.

## Example
```lean
example : toComplex (5 : ℝ) = (5 : ℂ) := by simp [toComplex]
example : toComplex ((3 : ℂ) + 4*I) = (3 : ℂ) + 4*I := by simp [toComplex]
```
-/
noncomputable
def toComplex {𝕜} [RCLike 𝕜] (x : 𝕜) : ℂ := ⟨re x, im x⟩

/--
Convert a complex number to a scalar type `𝕜`.

Uses the algebra map and the imaginary unit `I` to reconstruct the value in the target type.
This is the inverse of `toComplex` when `𝕜` can represent complex numbers.

## Example
```lean
example : fromComplex ℂ ((3 : ℂ) + 4*I) = (3 : ℂ) + 4*I := by simp [fromComplex]
```
-/
noncomputable
def fromComplex (𝕜 : Type*) [RCLike 𝕜] (x : ℂ) : 𝕜 := 𝓚 (x.re) + 𝓚 (x.im) * I

variable {𝕜} [RCLike 𝕜]

/-- `fromComplex` is the left inverse of `toComplex`. -/
@[simp]
theorem fromComplex_toComplex (x : 𝕜) : fromComplex 𝕜 (toComplex x) = x := by
  simp[fromComplex,toComplex]

/-- `toReal` is the left inverse of `fromReal` when applied to real numbers. -/
@[simp]
theorem toReal_fromReal (x : ℝ) : toReal (fromReal 𝕜 x) = x := by
  simp[fromReal,toReal]
