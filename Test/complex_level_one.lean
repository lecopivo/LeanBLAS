import LeanBLAS

open BLAS CBLAS

def test_complex_dot : IO Unit := do
  -- Create two complex vectors
  let x := #c64[⟨1.0, 0.0⟩, ⟨0.0, 1.0⟩]  -- [1+0i, 0+1i]
  let y := #c64[⟨1.0, 0.0⟩, ⟨0.0, -1.0⟩] -- [1+0i, 0-1i]
  
  -- Compute conjugate dot product: conj(x) · y
  -- Expected: conj(1+0i)*(1+0i) + conj(0+1i)*(0-1i)
  --         = (1-0i)*(1+0i) + (0-1i)*(0-1i)
  --         = 1 + 0i + 0 - 1i²
  --         = 1 + 1 = 2+0i
  let result_conj := dot 2 x 0 1 y 0 1
  IO.println s!"Conjugate dot product (zdotc): {result_conj}"
  
  -- Compute unconjugated dot product: x · y  
  -- Expected: (1+0i)*(1+0i) + (0+1i)*(0-1i)
  --         = 1 + 0i + 0 + 1i²
  --         = 1 - 1 = 0+0i
  let result_unconj := unconjugated_dot 2 x 0 1 y 0 1
  IO.println s!"Unconjugated dot product (zdotu): {result_unconj}"

def test_complex_norm : IO Unit := do
  -- Create a complex vector
  let x := #c64[⟨3.0, 4.0⟩, ⟨0.0, 0.0⟩]  -- [3+4i, 0+0i]
  
  -- Compute Euclidean norm
  -- Expected: sqrt(|3+4i|² + |0|²) = sqrt(9+16 + 0) = sqrt(25) = 5
  let norm := nrm2 2 x 0 1
  IO.println s!"Norm of [{⟨3.0, 4.0⟩}, {⟨0.0, 0.0⟩}]: {norm}"
  
  -- Compute sum of absolute values
  -- Expected: |3|+|4| + |0|+|0| = 7
  let sum_abs := asum 2 x 0 1
  IO.println s!"Sum of absolute values: {sum_abs}"

def test_complex_axpy : IO Unit := do
  -- Test Y = alpha*X + Y
  let x := #c64[⟨1.0, 0.0⟩, ⟨0.0, 1.0⟩]     -- [1+0i, 0+1i]
  let mut y := #c64[⟨2.0, 0.0⟩, ⟨0.0, 2.0⟩] -- [2+0i, 0+2i]
  let alpha := ComplexFloat.mk 2.0 0.0        -- 2+0i
  
  -- Expected: y = 2*(1+0i, 0+1i) + (2+0i, 0+2i) = (4+0i, 0+4i)
  y := axpy 2 alpha x 0 1 y 0 1
  IO.println s!"After axpy with alpha=2: {y.toComplexFloatArray}"

def main : IO Unit := do
  IO.println "=== Complex Level 1 BLAS Tests ==="
  IO.println ""
  
  IO.println "--- Dot Product Tests ---"
  test_complex_dot
  IO.println ""
  
  IO.println "--- Norm Tests ---"
  test_complex_norm
  IO.println ""
  
  IO.println "--- AXPY Test ---"
  test_complex_axpy