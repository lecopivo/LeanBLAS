import LeanBLAS.ComplexFloat

namespace BLAS


/-- `K` is either real or complex number, `R` is the type of the real part of `K`.

This class is used to define function either for real or complex numbers.

 -/
class Scalar (R : outParam (Type _)) (K : Type _) extends Add K, Sub K, Mul K, Div K, Neg K where
  intro ::

  mk : R → R→ K
  real : K → R
  imag : K → R
  conj : K → K

  isReal : Bool

  ofNat : Nat → K
  ofInt : Int → K

  abs : K → R

  exp : K → K
  log : K → K
  sin : K → K
  cos : K → K
  tan : K → K
  asin : K → K
  acos : K → K
  atan : K → K
  sinh : K → K
  cosh : K → K
  tanh : K → K
  asinh : K → K
  acosh : K → K
  atanh : K → K

  pow : K → K → K
  sqrt : K → K
  cbrt : K → K

  floor : K → K
  ceil : K → K
  round : K → K

  isFinite : K → Bool
  isNaN : K → Bool
  isInf : K → Bool


instance [Scalar R K] : OfNat K n where
  ofNat := Scalar.ofNat n


instance : Scalar Float Float where

  mk x _ := x
  real x := x
  imag _ := 0
  conj x := x

  isReal := true

  ofNat n := Float.ofNat n
  ofInt n := Float.ofInt n

  abs x := x.abs

  exp x := x.exp
  log x := x.log
  sin x := x.sin
  cos x := x.cos
  tan x := x.tan
  asin x := x.asin
  acos x := x.acos
  atan x := x.atan
  sinh x := x.sinh
  cosh x := x.cosh
  tanh x := x.tanh
  asinh x := x.asinh
  acosh x := x.acosh
  atanh x := x.atanh

  pow x y := x.pow y
  sqrt x := x.sqrt
  cbrt x := x.cbrt

  floor x := x.floor
  ceil x := x.ceil
  round x := x.round

  isFinite x := x.isFinite
  isNaN x := x.isNaN
  isInf x := x.isInf


instance : Scalar Float ComplexFloat where

  mk x y := ⟨x,y⟩
  real z := z.x
  imag z := z.y
  conj z := z.conj

  isReal := true

  ofNat n := ⟨.ofNat n, 0⟩
  ofInt n := ⟨.ofInt n, 0⟩

  abs x := x.abs

  exp x := x.exp
  log x := x.log
  sin x := x.sin
  cos x := x.cos
  tan x := x.tan
  asin x := x.asin
  acos x := x.acos
  atan x := x.atan
  sinh x := x.sinh
  cosh x := x.cosh
  tanh x := x.tanh
  asinh x := x.asinh
  acosh x := x.acosh
  atanh x := x.atanh

  pow x y := x.pow y
  sqrt x := x.sqrt
  cbrt x := x.cbrt

  floor x := x.floor
  ceil x := x.ceil
  round x := x.round

  isFinite x := x.isFinite
  isNaN x := x.isNaN
  isInf x := x.isInf
