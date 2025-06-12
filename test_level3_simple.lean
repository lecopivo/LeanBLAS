import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

open BLAS CBLAS

def approxEq (x y : Float) : Bool :=
  (x - y).abs < 0.00001

def testDGEMM : IO Unit := do
  IO.println "Testing DGEMM (Matrix Multiplication)"
  
  -- Create test matrices
  -- A = [1 2; 3 4] (2x2)
  -- B = [5 6; 7 8] (2x2)
  -- C = [0 0; 0 0] (2x2)
  let A := Float64Array.mk #[1.0, 2.0, 3.0, 4.0]
  let B := Float64Array.mk #[5.0, 6.0, 7.0, 8.0]
  let C := Float64Array.mk #[0.0, 0.0, 0.0, 0.0]
  
  -- Compute C = 1.0 * A * B + 0.0 * C
  let result := dgemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                     2 2 2 1.0 A 0 2 B 0 2 0.0 C 0 2
  
  -- Expected: A*B = [19 22; 43 50]
  let expected := #[19.0, 22.0, 43.0, 50.0]
  
  IO.println s!"A = {A.toFloatArray}"
  IO.println s!"B = {B.toFloatArray}"
  IO.println s!"Result = {result.toFloatArray}"
  
  let allCorrect := (result.toFloatArray.1.zip expected).all (fun (a, b) => approxEq a b)
  if allCorrect then
    IO.println "✓ DGEMM test passed!"
  else
    IO.println "✗ DGEMM test failed!"
    for i in [:4] do
      IO.println s!"  result[{i}] = {result.toFloatArray.1[i]!}, expected = {expected[i]!}"

def testDSYRK : IO Unit := do
  IO.println "\nTesting DSYRK (Symmetric Rank-K Update)"
  
  -- A = [1 2; 3 4] (2x2)
  -- C = [0 0; 0 0] (2x2)
  let A := Float64Array.mk #[1.0, 2.0, 3.0, 4.0]
  let C := Float64Array.mk #[0.0, 0.0, 0.0, 0.0]
  
  -- Compute C = 1.0 * A * A^T + 0.0 * C
  let result := dsyrk Order.RowMajor Uplo.Upper Transpose.NoTrans 
                     2 2 1.0 A 0 2 0.0 C 0 2
  
  -- Expected: A*A^T = [5 11; 11 25] (only upper triangle stored)
  let expected := #[5.0, 11.0, 11.0, 25.0]
  
  IO.println s!"A = {A.toFloatArray}"
  IO.println s!"Result = {result.toFloatArray}"
  
  -- Check upper triangle (elements 0, 1, 3)
  let upperCorrect := approxEq result.toFloatArray.1[0]! expected[0]! &&
                      approxEq result.toFloatArray.1[1]! expected[1]! &&
                      approxEq result.toFloatArray.1[3]! expected[3]!
  
  if upperCorrect then
    IO.println "✓ DSYRK test passed!"
  else
    IO.println "✗ DSYRK test failed!"

def testDTRSM : IO Unit := do
  IO.println "\nTesting DTRSM (Triangular System Solve)"
  
  -- A = [2 0; 1 3] (lower triangular)
  -- B = [4 6; 7 9] (2x2)
  let A := Float64Array.mk #[2.0, 0.0, 1.0, 3.0]
  let B := Float64Array.mk #[4.0, 6.0, 7.0, 9.0]
  
  -- Solve A * X = B for X
  let result := dtrsm Order.RowMajor Side.Left Uplo.Lower Transpose.NoTrans Diag.NonUnit
                     2 2 1.0 A 0 2 B 0 2
  
  -- Expected: X = [2 3; 5/3 2]
  let expected := #[2.0, 3.0, 5.0/3.0, 2.0]
  
  IO.println s!"A = {A.toFloatArray}"
  IO.println s!"B = {B.toFloatArray}"
  IO.println s!"Result = {result.toFloatArray}"
  
  let allCorrect := (result.toFloatArray.1.zip expected).all (fun (a, b) => approxEq a b)
  if allCorrect then
    IO.println "✓ DTRSM test passed!"
  else
    IO.println "✗ DTRSM test failed!"
    for i in [:4] do
      IO.println s!"  result[{i}] = {result.toFloatArray.1[i]!}, expected = {expected[i]!}"

def main : IO Unit := do
  IO.println "=== Level 3 BLAS Simple Tests ==="
  IO.println "Testing matrix-matrix operations\n"
  
  testDGEMM
  testDSYRK
  testDTRSM
  
  IO.println "\n=== Test Suite Complete ==="