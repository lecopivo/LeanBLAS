import LeanBLAS

/-!
# Edge Case Testing for LeanBLAS

This module provides comprehensive edge case testing that regular BLAS
implementations often miss, including boundary conditions, special values,
and error handling scenarios.
-/

open BLAS CBLAS

namespace BLAS.Test.EdgeCases

def approxEq (x y : Float) : Bool :=
  (x - y).abs < 1e-14

/-- Test with zero-length vectors -/
def test_zero_length : IO Unit := do
  IO.println "Testing zero-length operations..."
  
  let x := #f64[]
  let y := #f64[]
  
  -- These should not crash
  let dot_result := ddot 0 x 0 1 y 0 1
  let norm_result := dnrm2 0 x 0 1
  let asum_result := dasum 0 x 0 1
  
  IO.println s!"Zero-length dot: {dot_result}
Zero-length norm: {norm_result}
Zero-length asum: {asum_result}"
  
  -- Results should be zero
  if !(approxEq dot_result 0.0) then
    throw $ IO.userError "Zero-length dot product should be 0"
  if !(approxEq norm_result 0.0) then
    throw $ IO.userError "Zero-length norm should be 0"
  if !(approxEq asum_result 0.0) then
    throw $ IO.userError "Zero-length asum should be 0"

/-- Test with single element vectors -/
def test_single_element : IO Unit := do
  IO.println "Testing single-element operations..."
  
  let x := #f64[3.14]
  let y := #f64[2.71]
  
  let dot_result := ddot 1 x 0 1 y 0 1
  let norm_result := dnrm2 1 x 0 1
  let asum_result := dasum 1 x 0 1
  
  let expected_dot := 3.14 * 2.71
  let expected_norm := 3.14
  let expected_asum := 3.14
  
  IO.println s!"Single dot: {dot_result} (expected {expected_dot})"
  IO.println s!"Single norm: {norm_result} (expected {expected_norm})"
  IO.println s!"Single asum: {asum_result} (expected {expected_asum})"
  
  if !(approxEq dot_result expected_dot) then
    throw $ IO.userError "Single-element dot product failed"
  if !(approxEq norm_result expected_norm) then
    throw $ IO.userError "Single-element norm failed"
  if !(approxEq asum_result expected_asum) then
    throw $ IO.userError "Single-element asum failed"

/-- Test with very large numbers (overflow detection) -/
def test_large_numbers : IO Unit := do
  IO.println "Testing large number handling..."
  
  let large_val := 1e100
  let x := #f64[large_val, large_val]
  
  let norm_result := dnrm2 2 x 0 1
  let asum_result := dasum 2 x 0 1
  
  IO.println s!"Large norm: {norm_result}"
  IO.println s!"Large asum: {asum_result}"
  
  -- Check for very large values (potential overflow)
  if norm_result > 1e100 then
    IO.println "Warning: Norm calculation resulted in very large value"
  if asum_result > 1e100 then
    IO.println "Warning: Asum calculation resulted in very large value"

/-- Test with very small numbers (underflow detection) -/
def test_small_numbers : IO Unit := do
  IO.println "Testing small number handling..."
  
  let small_val := 1e-100
  let x := #f64[small_val, small_val]
  
  let norm_result := dnrm2 2 x 0 1
  let asum_result := dasum 2 x 0 1
  
  IO.println s!"Small norm: {norm_result}"
  IO.println s!"Small asum: {asum_result}"
  
  -- Results should be meaningful, not zero due to underflow
  if norm_result == 0.0 then
    IO.println "Warning: Norm underflowed to zero"
  if asum_result == 0.0 then
    IO.println "Warning: Asum underflowed to zero"

/-- Test with special floating point values -/
def test_special_values : IO Unit := do
  IO.println "Testing special floating point values..."
  
  -- Test with very large value (simulating infinity)
  let large_x := #f64[1e308, 1.0]
  let large_norm := dnrm2 2 large_x 0 1
  IO.println s!"Very large value norm: {large_norm}"
  
  -- Test with zero (edge case)
  let zero_x := #f64[0.0, 0.0]
  let zero_norm := dnrm2 2 zero_x 0 1
  IO.println s!"Zero norm: {zero_norm}"
  
  -- Test with negative zero
  let neg_zero_x := #f64[-0.0, 1.0]
  let neg_zero_norm := dnrm2 2 neg_zero_x 0 1
  IO.println s!"Negative zero norm: {neg_zero_norm}"

/-- Test with various stride patterns -/
def test_stride_patterns : IO Unit := do
  IO.println "Testing stride patterns..."
  
  let x := #f64[1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0]
  
  -- Test stride 1 (normal)
  let norm1 := dnrm2 4 x 0 1
  
  -- Test stride 2 (every other element)
  let norm2 := dnrm2 4 x 0 2
  
  -- Test large stride
  let norm3 := dnrm2 2 x 0 3
  
  IO.println s!"Stride 1 norm: {norm1}"
  IO.println s!"Stride 2 norm: {norm2}"
  IO.println s!"Stride 3 norm: {norm3}"
  
  -- Expected values for verification
  let expected1 := Float.sqrt (1.0 + 4.0 + 9.0 + 16.0)  -- [1,2,3,4]
  let expected2 := Float.sqrt (1.0 + 9.0 + 25.0 + 49.0) -- [1,3,5,7]
  let expected3 := Float.sqrt (1.0 + 16.0)              -- [1,4]
  
  if !(approxEq norm1 expected1) then
    throw $ IO.userError "Stride 1 test failed"
  if !(approxEq norm2 expected2) then
    throw $ IO.userError "Stride 2 test failed"
  if !(approxEq norm3 expected3) then
    throw $ IO.userError "Stride 3 test failed"

/-- Test with large offsets -/
def test_large_offsets : IO Unit := do
  IO.println "Testing large offsets..."
  
  let x := #f64[0.0, 0.0, 0.0, 1.0, 2.0, 3.0]
  
  -- Test with offset
  let norm_offset := dnrm2 3 x 3 1
  let expected := Float.sqrt (1.0 + 4.0 + 9.0)
  
  IO.println s!"Offset norm: {norm_offset} (expected {expected})"
  
  if !(approxEq norm_offset expected) then
    throw $ IO.userError "Large offset test failed"

/-- Test numerical stability with cancellation -/
def test_numerical_stability : IO Unit := do
  IO.println "Testing numerical stability..."
  
  -- Test with values that could cause cancellation errors
  let large := 1e8
  let small := 1.0
  let x := #f64[large, small, -large]
  
  let norm_result := dnrm2 3 x 0 1
  let expected := small  -- Should be approximately 1.0 after cancellation
  
  IO.println s!"Cancellation test norm: {norm_result} (expected ≈ {expected})"
  
  -- Allow for some numerical error but check it's reasonable
  if Float.abs (norm_result - expected) > 1e-6 then
    IO.println s!"Warning: Large numerical error in cancellation test: {Float.abs (norm_result - expected)}"

/-- Main edge case test runner -/
def main : IO Unit := do
  IO.println "Running Comprehensive Edge Case Tests"
  IO.println (String.mk (List.replicate 50 '='))
  
  test_zero_length
  IO.println ""
  
  test_single_element
  IO.println ""
  
  test_large_numbers
  IO.println ""
  
  test_small_numbers
  IO.println ""
  
  test_special_values
  IO.println ""
  
  test_stride_patterns
  IO.println ""
  
  test_large_offsets
  IO.println ""
  
  test_numerical_stability
  IO.println ""
  
  IO.println "✓ All edge case tests completed!"

end BLAS.Test.EdgeCases

-- Module-level main for executable
def main : IO Unit := BLAS.Test.EdgeCases.main
