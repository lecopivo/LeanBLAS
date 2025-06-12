import LeanBLAS

/-!
# Debug Property Test Failures

This module investigates the property test failures with more detailed analysis.
-/

open BLAS CBLAS

namespace BLAS.Test.PropertyDebug

/-- Relative error calculation -/
def relativeError (expected actual : Float) : Float :=
  if expected == 0 then
    actual.abs
  else
    ((expected - actual) / expected).abs

/-- Test norm squared equals dot with self with detailed output -/
def test_norm_squared_detailed : IO Unit := do
  IO.println "Testing norm² = dot(x,x) property with detailed analysis..."
  IO.println "=================================================="
  
  -- Test 1: Simple case [3, 4] -> norm = 5
  let x1 := #f64[3.0, 4.0]
  let norm1 := dnrm2 2 x1 0 1
  let dot1 := ddot 2 x1 0 1 x1 0 1
  IO.println s!"\nTest 1: x = [3, 4]"
  IO.println s!"  norm(x) = {norm1}"
  IO.println s!"  norm²(x) = {norm1 * norm1}"
  IO.println s!"  dot(x,x) = {dot1}"
  IO.println s!"  Absolute error: {Float.abs (norm1 * norm1 - dot1)}"
  IO.println s!"  Relative error: {relativeError dot1 (norm1 * norm1)}"
  
  -- Test 2: Large values (potential overflow in intermediate calculations)
  let x2 := #f64[1e150, 1e150]
  let norm2 := dnrm2 2 x2 0 1
  let dot2 := ddot 2 x2 0 1 x2 0 1
  IO.println s!"\nTest 2: x = [1e150, 1e150]"
  IO.println s!"  norm(x) = {norm2}"
  IO.println s!"  norm²(x) = {norm2 * norm2}"
  IO.println s!"  dot(x,x) = {dot2}"
  IO.println s!"  Relative error: {relativeError dot2 (norm2 * norm2)}"
  
  -- Test 3: Small values (potential underflow)
  let x3 := #f64[1e-150, 1e-150]
  let norm3 := dnrm2 2 x3 0 1
  let dot3 := ddot 2 x3 0 1 x3 0 1
  IO.println s!"\nTest 3: x = [1e-150, 1e-150]"
  IO.println s!"  norm(x) = {norm3}"
  IO.println s!"  norm²(x) = {norm3 * norm3}"
  IO.println s!"  dot(x,x) = {dot3}"
  if dot3 == 0 && norm3 == 0 then
    IO.println s!"  Both underflowed to zero"
  else
    IO.println s!"  Relative error: {relativeError dot3 (norm3 * norm3)}"
  
  -- Test 4: Mixed magnitudes (numerical stability test)
  let x4 := #f64[1.0, 1e-8, 1e8]
  let norm4 := dnrm2 3 x4 0 1
  let dot4 := ddot 3 x4 0 1 x4 0 1
  IO.println s!"\nTest 4: x = [1.0, 1e-8, 1e8]"
  IO.println s!"  norm(x) = {norm4}"
  IO.println s!"  norm²(x) = {norm4 * norm4}"
  IO.println s!"  dot(x,x) = {dot4}"
  IO.println s!"  Relative error: {relativeError dot4 (norm4 * norm4)}"

/-- Test AXPY linearity with detailed analysis -/
def test_axpy_linearity_detailed : IO Unit := do
  IO.println "\n\nTesting AXPY linearity property..."
  IO.println "================================="
  IO.println "Testing: alpha*x + beta*x + y = (alpha + beta)*x + y"
  
  -- Test with simple values
  let x := #f64[1.0, 2.0, 3.0]
  let y := #f64[4.0, 5.0, 6.0]
  let alpha := 2.0
  let beta := 3.0
  
  -- Method 1: (alpha + beta) * x + y
  let y1 := dcopy 3 y 0 1 (#f64[0.0, 0.0, 0.0]) 0 1
  let result1 := daxpy 3 (alpha + beta) x 0 1 y1 0 1
  
  -- Method 2: alpha * x + y, then beta * x + result
  let y2 := dcopy 3 y 0 1 (#f64[0.0, 0.0, 0.0]) 0 1
  let temp := daxpy 3 alpha x 0 1 y2 0 1
  let result2 := daxpy 3 beta x 0 1 temp 0 1
  
  IO.println s!"\nTest values:"
  IO.println s!"  x = {x.toFloatArray}"
  IO.println s!"  y = {y.toFloatArray}"
  IO.println s!"  alpha = {alpha}, beta = {beta}"
  IO.println s!"\nMethod 1: (alpha + beta)*x + y = {result1.toFloatArray}"
  IO.println s!"Method 2: alpha*x + (beta*x + y) = {result2.toFloatArray}"
  
  -- Check element-wise differences
  IO.println "\nElement-wise comparison:"
  for i in [0:3] do
    let v1 := result1.toFloatArray.get! i
    let v2 := result2.toFloatArray.get! i
    let diff := Float.abs (v1 - v2)
    let relErr := if v2 == 0 then diff else diff / v2.abs
    IO.println s!"  [{i}]: {v1} vs {v2}, diff = {diff}, rel_err = {relErr}"
  
  -- The actual property being tested in Property.lean is WRONG
  IO.println "\n⚠️  The property test is incorrect!"
  IO.println "The test compares:"
  IO.println "  y1 = alpha*x + y"
  IO.println "  y2 = beta*x + y"
  IO.println "  y_combined = (alpha + beta)*x + y"
  IO.println "  y_sum = y1 + y2 = alpha*x + y + beta*x + y = (alpha + beta)*x + 2*y"
  IO.println "So y_sum ≠ y_combined because of the extra y term!"

/-- Propose better properties to test -/
def better_properties : IO Unit := do
  IO.println "\n\nBetter AXPY properties to test:"
  IO.println "==============================="
  
  IO.println "\n1. Distributivity: alpha*(x + y) = alpha*x + alpha*y"
  let x := #f64[1.0, 2.0]
  let y := #f64[3.0, 4.0]
  let alpha := 2.5
  
  -- Compute x + y
  let x_plus_y := daxpy 2 1.0 x 0 1 (dcopy 2 y 0 1 (#f64[0.0, 0.0]) 0 1) 0 1
  -- Compute alpha*(x + y)
  let lhs := dscal 2 alpha x_plus_y 0 1
  
  -- Compute alpha*x + alpha*y
  let ax := dscal 2 alpha (dcopy 2 x 0 1 (#f64[0.0, 0.0]) 0 1) 0 1
  let ay := dscal 2 alpha (dcopy 2 y 0 1 (#f64[0.0, 0.0]) 0 1) 0 1
  let rhs := daxpy 2 1.0 ax 0 1 ay 0 1
  
  IO.println s!"  x = {x.toFloatArray}, y = {y.toFloatArray}, alpha = {alpha}"
  IO.println s!"  alpha*(x + y) = {lhs.toFloatArray}"
  IO.println s!"  alpha*x + alpha*y = {rhs.toFloatArray}"
  
  IO.println "\n2. Zero scalar: 0*x + y = y"
  let result := daxpy 2 0.0 x 0 1 (dcopy 2 y 0 1 (#f64[0.0, 0.0]) 0 1) 0 1
  IO.println s!"  0*x + y = {result.toFloatArray}"
  IO.println s!"  y = {y.toFloatArray}"
  
  IO.println "\n3. Identity: 1*x + 0 = x"
  let zero := #f64[0.0, 0.0]
  let result2 := daxpy 2 1.0 x 0 1 zero 0 1
  IO.println s!"  1*x + 0 = {result2.toFloatArray}"
  IO.println s!"  x = {x.toFloatArray}"

/-- Main test runner -/
def main : IO Unit := do
  test_norm_squared_detailed
  test_axpy_linearity_detailed
  better_properties

end BLAS.Test.PropertyDebug

-- Module-level main
def main : IO Unit := BLAS.Test.PropertyDebug.main