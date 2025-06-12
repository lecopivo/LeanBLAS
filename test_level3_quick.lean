import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

open BLAS CBLAS

/-- Quick test to verify Level 3 BLAS functionality -/
def test_basic_gemm : IO Unit := do
  IO.println "Testing basic GEMM functionality..."
  
  -- Create simple 2x2 matrices: A = [[1,2],[3,4]], B = [[5,6],[7,8]]
  let A := #f64[1.0, 2.0, 3.0, 4.0]  -- 2x2 matrix in row-major order
  let B := #f64[5.0, 6.0, 7.0, 8.0]  -- 2x2 matrix in row-major order  
  let C := #f64[0.0, 0.0, 0.0, 0.0]  -- 2x2 result matrix initialized to zero
  
  -- Compute C = 1.0 * A * B + 0.0 * C
  let result := gemm Order.RowMajor Transpose.NoTrans Transpose.NoTrans 
                     2 2 2           -- M=2, N=2, K_dim=2
                     1.0             -- alpha=1.0  
                     A 0 2           -- A, offset=0, lda=2
                     B 0 2           -- B, offset=0, ldb=2
                     0.0             -- beta=0.0
                     C 0 2           -- C, offset=0, ldc=2
  
  IO.println s!"Result matrix: {result}"
  -- Expected: A*B = [[1*5+2*7, 1*6+2*8], [3*5+4*7, 3*6+4*8]] = [[19,22],[43,50]]
  
  IO.println "✓ GEMM test completed"

def main : IO Unit := do
  IO.println "=== Level 3 BLAS Quick Test ==="
  test_basic_gemm
  IO.println "=== All tests completed ==="