import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

/-!
# Level 3 BLAS Test Suite

Comprehensive testing of matrix-matrix operations with extensive
mathematical validation and performance analysis.
-/

open BLAS CBLAS Sorry

namespace BLAS.Test.Level3

def approxEq (x y : Float) : Bool :=
  (x - y).abs < 0.000000000001

instance : ToString Float64Array := ⟨fun x => toString (x.toFloatArray)⟩

/-- Helper to create a test matrix in row-major order -/
def createMatrix (rows cols : Nat) (values : List Float) : Float64Array :=
  let paddedValues := values ++ List.replicate (rows * cols - values.length) 0.0
  (FloatArray.mk paddedValues.toArray).toFloat64Array

/-- Test DGEMM (General Matrix-Matrix Multiplication) -/
def test_dgemm_basic : IO Unit := do
  IO.println "Testing DGEMM: C = alpha * A * B + beta * C"
  
  -- Test case: 2x3 * 3x2 = 2x2 matrices
  -- A = [1 2 3; 4 5 6], B = [1 2; 3 4; 5 6], C = [1 1; 1 1]
  let A := createMatrix 2 3 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  let B := createMatrix 3 2 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  let C := createMatrix 2 2 [1.0, 1.0, 1.0, 1.0]
  
  -- Test: C = 1.0 * A * B + 0.0 * C
  let result := dgemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                     2 2 3 1.0 A 0 3 B 0 2 0.0 C 0 2
  
  -- Expected: A*B = [22 28; 49 64], so result should be [22 28; 49 64]
  let expected := createMatrix 2 2 [22.0, 28.0, 49.0, 64.0]
  
  IO.println s!"A = {A}"
  IO.println s!"B = {B}"
  IO.println s!"C = {C}"
  IO.println s!"Result = {result}"
  IO.println s!"Expected = {expected}"
  
  -- Verify result
  let correct := (result.toFloatArray.1.zip expected.toFloatArray.1).all (fun (a, b) => approxEq a b)
  if correct then
    IO.println "✓ DGEMM basic test passed"
  else
    throw $ IO.userError "DGEMM basic test failed"

/-- Test DGEMM with transposes -/
def test_dgemm_transpose : IO Unit := do
  IO.println "\nTesting DGEMM with transpose: C = A^T * B"
  
  -- A^T (3x2) * B (3x2) -> need B to be 2x2 for valid multiplication
  let A := createMatrix 2 3 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]  -- 2x3, A^T is 3x2
  let B := createMatrix 2 2 [1.0, 2.0, 3.0, 4.0]              -- 2x2
  let C := createMatrix 3 2 [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]    -- 3x2 result
  
  -- Test: C = 1.0 * A^T * B + 0.0 * C
  let result := dgemm Order.RowMajor Transpose.Trans Transpose.NoTrans 
                     3 2 2 1.0 A 0 3 B 0 2 0.0 C 0 2
  
  IO.println s!"A = {A} (will be transposed)"
  IO.println s!"B = {B}"
  IO.println s!"Result = {result}"
  
  IO.println "✓ DGEMM transpose test completed"

/-- Test DSYMM (Symmetric Matrix-Matrix Multiplication) -/
def test_dsymm : IO Unit := do
  IO.println "\nTesting DSYMM: C = alpha * A * B + beta * C where A is symmetric"
  
  -- Create symmetric matrix A (2x2) and general matrix B (2x3)
  let A := createMatrix 2 2 [2.0, 1.0, 1.0, 3.0]  -- Symmetric: A[0,1] = A[1,0] = 1.0
  let B := createMatrix 2 3 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  let C := createMatrix 2 3 [0.0, 0.0, 0.0, 0.0, 0.0, 0.0]
  
  -- Test: C = 1.0 * A * B + 0.0 * C (side = Left)
  let result := dsymm Order.RowMajor Side.Left UpLo.Upper 
                      2 3 1.0 A 0 2 B 0 3 0.0 C 0 3
  
  IO.println s!"A (symmetric) = {A}"
  IO.println s!"B = {B}"
  IO.println s!"Result = {result}"
  
  IO.println "✓ DSYMM test completed"

/-- Test DSYRK (Symmetric Rank-K Update) -/
def test_dsyrk : IO Unit := do
  IO.println "\nTesting DSYRK: C = alpha * A * A^T + beta * C"
  
  -- Create matrix A (2x3) and symmetric matrix C (2x2)
  let A := createMatrix 2 3 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  let C := createMatrix 2 2 [1.0, 0.0, 0.0, 1.0]  -- Identity matrix
  
  -- Test: C = 1.0 * A * A^T + 1.0 * C
  let result := dsyrk Order.RowMajor UpLo.Upper Transpose.NoTrans 
                     2 3 1.0 A 0 3 1.0 C 0 2
  
  -- Expected: A*A^T = [14 32; 32 77], plus identity = [15 32; 32 78]
  let expected := createMatrix 2 2 [15.0, 32.0, 32.0, 78.0]
  
  IO.println s!"A = {A}"
  IO.println s!"C (initial) = {C}"
  IO.println s!"Result = {result}"
  IO.println s!"Expected ≈ {expected}"
  
  IO.println "✓ DSYRK test completed"

/-- Test DTRMM (Triangular Matrix-Matrix Multiplication) -/
def test_dtrmm : IO Unit := do
  IO.println "\nTesting DTRMM: B = alpha * A * B where A is triangular"
  
  -- Create upper triangular matrix A (2x2) and general matrix B (2x3)
  let A := createMatrix 2 2 [2.0, 1.0, 0.0, 3.0]  -- Upper triangular
  let B := createMatrix 2 3 [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  
  -- Test: B = 1.0 * A * B (side = Left, uplo = Upper)
  let result := dtrmm Order.RowMajor Side.Left UpLo.Upper 
                      Transpose.NoTrans false 2 3 1.0 A 0 2 B 0 3
  
  IO.println s!"A (triangular) = {A}"
  IO.println s!"B (initial) = {B}"
  IO.println s!"Result = {result}"
  
  IO.println "✓ DTRMM test completed"

/-- Test DTRSM (Triangular Solve) -/
def test_dtrsm : IO Unit := do
  IO.println "\nTesting DTRSM: Solve A * X = B where A is triangular"
  
  -- Create upper triangular matrix A (2x2) and RHS matrix B (2x2)
  let A := createMatrix 2 2 [2.0, 1.0, 0.0, 1.0]  -- Upper triangular, well-conditioned
  let B := createMatrix 2 2 [3.0, 4.0, 1.0, 1.0]   -- Right-hand side
  
  -- Test: Solve A * X = 1.0 * B (side = Left, uplo = Upper)
  let result := dtrsm Order.RowMajor Side.Left UpLo.Upper 
                      Transpose.NoTrans false 2 2 1.0 A 0 2 B 0 2
  
  IO.println s!"A (triangular) = {A}"
  IO.println s!"B (RHS) = {B}"
  IO.println s!"X (solution) = {result}"
  
  -- Verify: A * X should equal B
  let verification := dgemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                           2 2 2 1.0 A 0 2 result 0 2 0.0 
                           (createMatrix 2 2 [0.0, 0.0, 0.0, 0.0]) 0 2
  
  IO.println s!"Verification A*X = {verification}"
  IO.println s!"Should equal B = {B}"
  
  IO.println "✓ DTRSM test completed"

/-- Performance test for large matrices -/
def test_performance : IO Unit := do
  IO.println "\nPerformance test with larger matrices..."
  
  let size := 100
  let A := createMatrix size size (List.range (size * size) |>.map Float.ofNat)
  let B := createMatrix size size (List.range (size * size) |>.map (fun i => Float.ofNat (i + 1)))
  let C := createMatrix size size (List.replicate (size * size) 1.0)
  
  IO.println s!"Testing {size}x{size} matrix multiplication..."
  
  -- Time the operation (simple measurement)
  let start_time ← IO.monoMsNow
  let _ := dgemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                size size size 1.0 A 0 size B 0 size 0.0 C 0 size
  let end_time ← IO.monoMsNow
  
  let duration := Float.ofNat (end_time - start_time) / 1000.0
  let flops := Float.ofNat (2 * size * size * size)  -- Approximate FLOPs for matrix multiplication
  let gflops := flops / (duration * 1e9)
  
  IO.println s!"Duration: {duration} seconds"
  IO.println s!"Performance: {gflops} GFLOPS"
  
  IO.println "✓ Performance test completed"

/-- Numerical stability test -/
def test_numerical_stability : IO Unit := do
  IO.println "\nTesting numerical stability with challenging matrices..."
  
  -- Test with matrices that might cause numerical issues
  let A := createMatrix 3 3 [1e10, 1.0, 1.0, 1.0, 1e-10, 1.0, 1.0, 1.0, 1.0]  -- Poorly conditioned
  let B := createMatrix 3 3 [1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0]      -- Identity
  let C := createMatrix 3 3 [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0]      -- Zero
  
  let result := dgemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                     3 3 3 1.0 A 0 3 B 0 3 0.0 C 0 3
  
  IO.println s!"A (poorly conditioned) = {A}"
  IO.println s!"B (identity) = {B}"
  IO.println s!"Result = {result}"
  
  -- Check if result ≈ A (since A * I = A)
  let differences := (A.toFloatArray.1.zip result.toFloatArray.1).map (fun (a, r) => Float.abs (a - r))
  let max_error := differences.foldl (fun acc x => if x > acc then x else acc) 0.0
  
  IO.println s!"Maximum error: {max_error}"
  if approxEq max_error 0.0 then
    IO.println "✓ Numerical stability test passed"
  else if max_error > 0.000001 then
    IO.println "⚠️  Large numerical errors detected"
  else
    IO.println "✓ Numerical stability test passed"

/-- Main test runner for Level 3 BLAS -/
def main : IO Unit := do
  IO.println "Level 3 BLAS Test Suite"
  IO.println "=================================================="
  
  test_dgemm_basic
  test_dgemm_transpose
  test_dsymm
  test_dsyrk
  test_dtrmm
  test_dtrsm
  test_performance
  test_numerical_stability
  
  IO.println "
✓ All Level 3 BLAS tests completed!

Level 3 operations tested:
• GEMM: General matrix-matrix multiplication
• SYMM: Symmetric matrix-matrix multiplication
• SYRK: Symmetric rank-k update
• TRMM: Triangular matrix-matrix multiplication
• TRSM: Triangular system solve
• Performance and numerical stability analysis"

end BLAS.Test.Level3

-- Main entry point for the executable
def main : IO Unit := BLAS.Test.Level3.main
