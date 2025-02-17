import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic

import LeanBLAS.Util

namespace BLAS

open Sorry RCLike

local notation "𝓚" => algebraMap ℝ _

noncomputable
def toReal {𝕜} [RCLike 𝕜] (x : 𝕜) : ℝ := re x

noncomputable
def fromReal (𝕜 : Type*) [RCLike 𝕜] (x : ℝ) : 𝕜 := 𝓚 (re x)

noncomputable
def toComplex {𝕜} [RCLike 𝕜] (x : 𝕜) : ℂ := ⟨re x, im x⟩

noncomputable
def fromComplex (𝕜 : Type*) [RCLike 𝕜] (x : ℂ) : 𝕜 := 𝓚 (x.re) + 𝓚 (x.im) * I

variable {𝕜} [RCLike 𝕜]

@[simp]
theorem fromComplex_toComplex (x : 𝕜) : fromComplex 𝕜 (toComplex x) = x := by
  simp[fromComplex,toComplex]

@[simp]
theorem toReal_fromReal (x : ℝ) : toReal (fromReal 𝕜 x) = x := by
  simp[fromReal,toReal]
