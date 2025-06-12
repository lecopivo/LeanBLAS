import LeanBLAS

/-!
# Property-Based Testing Framework for LeanBLAS

This module provides a comprehensive property-based testing framework
that generates random test cases and validates mathematical properties
of BLAS operations.
-/

open BLAS CBLAS

namespace BLAS.Test

/-- Random number generator state -/
structure RandState where
  seed : Nat
  next : Nat

/-- Generate a random Float64 in range [min, max] -/
def RandState.nextFloat (state : RandState) (min max : Float) : RandState × Float :=
  let newNext := (state.next * 1103515245 + 12345) % (2^31)
  let normalized := Float.ofNat newNext / Float.ofNat (2^31)
  let value := min + normalized * (max - min)
  ({ state with next := newNext }, value)

/-- Generate a random Nat in range [0, max) -/
def RandState.nextNat (state : RandState) (max : Nat) : RandState × Nat :=
  let newNext := (state.next * 1103515245 + 12345) % (2^31)
  let value := newNext % max
  ({ state with next := newNext }, value)

/-- Generate a random Float64Array of given size -/
def RandState.nextFloat64Array (state : RandState) (size : Nat) (min max : Float) : RandState × Float64Array := Id.run do
  let mut currentState := state
  let mut values : Array Float := #[]
  for _ in [0:size] do
    let (newState, value) := currentState.nextFloat min max
    currentState := newState
    values := values.push value
  (currentState, (FloatArray.mk values).toFloat64Array)

/-- Create a zero Float64Array of given size -/
def zeroFloat64Array (size : Nat) : Float64Array :=
  let values := List.replicate size 0.0
  (FloatArray.mk values.toArray).toFloat64Array

/-- Property: dot product should be commutative -/
def prop_dot_commutative (n : Nat) (x y : Float64Array) : Bool :=
  if n == 0 ∨ x.size < n ∨ y.size < n then true
  else
    let dot1 := ddot n x 0 1 y 0 1
    let dot2 := ddot n y 0 1 x 0 1
    Float.abs (dot1 - dot2) < 1e-12

/-- Property: norm squared should equal dot product with self -/
def prop_norm_squared_eq_dot_self (n : Nat) (x : Float64Array) : Bool :=
  if n == 0 ∨ x.size < n then true
  else
    let norm := dnrm2 n x 0 1
    let dot_self := ddot n x 0 1 x 0 1
    -- Use relative error for better numerical stability
    if dot_self == 0.0 then
      norm == 0.0  -- Both should be zero
    else
      let rel_error := Float.abs ((norm * norm - dot_self) / dot_self)
      rel_error < 1e-10  -- Allow small relative error

/-- Property: axpy distributivity - (alpha + beta)*x + y = alpha*x + (beta*x + y) -/
def prop_axpy_linearity (n : Nat) (alpha beta : Float) (x y : Float64Array) : Bool :=
  if n == 0 ∨ x.size < n ∨ y.size < n then true
  else
    -- Method 1: (alpha + beta)*x + y
    let y_copy1 := dcopy n y 0 1 (zeroFloat64Array n) 0 1
    let result1 := daxpy n (alpha + beta) x 0 1 y_copy1 0 1
    
    -- Method 2: beta*x + y, then alpha*x + result
    let y_copy2 := dcopy n y 0 1 (zeroFloat64Array n) 0 1
    let temp := daxpy n beta x 0 1 y_copy2 0 1
    let result2 := daxpy n alpha x 0 1 temp 0 1
    
    -- Compare results
    let diff := daxpy n (-1.0) result1 0 1 result2 0 1
    let norm_diff := dnrm2 n diff 0 1
    let norm_result := dnrm2 n result1 0 1
    
    if norm_result == 0.0 then
      norm_diff < 1e-10
    else
      norm_diff / norm_result < 1e-10  -- Relative error

/-- Property: copy should preserve all elements -/
def prop_copy_preserves (n : Nat) (x y : Float64Array) : Bool :=
  if n == 0 ∨ x.size < n ∨ y.size < n then true
  else
    let y' := dcopy n x 0 1 y 0 1
    let dot_orig := ddot n x 0 1 x 0 1
    let dot_copy := ddot n y' 0 1 y' 0 1
    Float.abs (dot_orig - dot_copy) < 1e-12

/-- Test runner for a single property -/
def runProperty (prop : Nat → Float64Array → Float64Array → Bool) (numTests : Nat) : IO Bool := do
  let mut state : RandState := { seed := 42, next := 42 }
  let mut passed := 0
  
  for i in [0:numTests] do
    let (state1, n) := state.nextNat 100
    let n := n + 1  -- Ensure n > 0
    let (state2, x) := state1.nextFloat64Array n (-10.0) 10.0
    let (state3, y) := state2.nextFloat64Array n (-10.0) 10.0
    state := state3
    
    if prop n x y then
      passed := passed + 1
    else
      IO.println s!"Property failed on test {i + 1}: n={n}"
      return false
  
  IO.println s!"Property passed {passed}/{numTests} tests"
  return passed == numTests

/-- Run property tests with single vector -/
def runPropertySingle (prop : Nat → Float64Array → Bool) (numTests : Nat) : IO Bool := do
  let mut state : RandState := { seed := 42, next := 42 }
  let mut passed := 0
  
  for i in [0:numTests] do
    let (state1, n) := state.nextNat 100
    let n := n + 1  -- Ensure n > 0
    let (state2, x) := state1.nextFloat64Array n (-10.0) 10.0
    state := state2
    
    if prop n x then
      passed := passed + 1
    else
      IO.println s!"Property failed on test {i + 1}: n={n}"
      return false
  
  IO.println s!"Property passed {passed}/{numTests} tests"
  return passed == numTests

/-- Run property tests with scalars and vectors -/
def runPropertyScalar (prop : Nat → Float → Float → Float64Array → Float64Array → Bool) (numTests : Nat) : IO Bool := do
  let mut state : RandState := { seed := 42, next := 42 }
  let mut passed := 0
  
  for i in [0:numTests] do
    let (state1, n) := state.nextNat 100
    let n := n + 1  -- Ensure n > 0
    let (state2, alpha) := state1.nextFloat (-10.0) 10.0
    let (state3, beta) := state2.nextFloat (-10.0) 10.0
    let (state4, x) := state3.nextFloat64Array n (-10.0) 10.0
    let (state5, y) := state4.nextFloat64Array n (-10.0) 10.0
    state := state5
    
    if prop n alpha beta x y then
      passed := passed + 1
    else
      IO.println s!"Property failed on test {i + 1}: n={n}, alpha={alpha}, beta={beta}"
      return false
  
  IO.println s!"Property passed {passed}/{numTests} tests"
  return passed == numTests

/-- Comprehensive property test suite -/
def main : IO Unit := do
  IO.println "Running Property-Based Tests for BLAS Level 1"
  IO.println (String.mk (List.replicate 50 '='))
  
  IO.println "\nTesting dot product commutativity..."
  let test1 ← runProperty prop_dot_commutative 1000
  
  IO.println "\nTesting norm squared equals dot with self..."
  let test2 ← runPropertySingle prop_norm_squared_eq_dot_self 1000
  
  IO.println "\nTesting axpy linearity..."
  let test3 ← runPropertyScalar prop_axpy_linearity 1000
  
  IO.println "\nTesting copy preservation..."
  let test4 ← runProperty prop_copy_preserves 1000
  
  if test1 ∧ test2 ∧ test3 ∧ test4 then
    IO.println "\n✓ All property tests passed!"
  else
    IO.println "\n✗ Some property tests failed!"
    throw $ IO.userError "Property tests failed"

end BLAS.Test

-- Module-level main for executable
def main : IO Unit := BLAS.Test.main
