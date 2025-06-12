
import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

def main : IO Unit := do
  -- Create small 2x2 matrices for quick test
  let A := #f64[1.0, 2.0, 3.0, 4.0]
  let B := #f64[5.0, 6.0, 7.0, 8.0]
  let C := #f64[0.0, 0.0, 0.0, 0.0]
  
  -- Perform matrix multiplication
  let result := BLAS.CBLAS.dgemm 
    BLAS.Order.RowMajor 
    BLAS.Transpose.NoTrans 
    BLAS.Transpose.NoTrans
    2 2 2  -- M, N, K dimensions
    1.0    -- alpha
    A 0 2  -- A matrix
    B 0 2  -- B matrix  
    0.0    -- beta
    C 0 2  -- C matrix
    
  IO.println "Test completed. Result computed successfully."
  IO.println s!"First element: {result.toFloatArray[0]!}"
  IO.println s!"Full result: {result.toFloatArray}"
