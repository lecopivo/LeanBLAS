import LeanBLAS

open BLAS CBLAS

def test_norm_squared : IO Unit := do
  -- Create a simple test vector
  let x := #f64[3.0, 4.0]  -- Should have norm 5
  let n := 2
  
  let norm := dnrm2 n x 0 1
  let dot_self := ddot n x 0 1 x 0 1
  
  IO.println s!"Vector: [3.0, 4.0]"
  IO.println s!"Norm: {norm}"
  IO.println s!"Norm squared: {norm * norm}"
  IO.println s!"Dot with self: {dot_self}"
  IO.println s!"Difference: {Float.abs (norm * norm - dot_self)}"
  
  -- Test with a larger vector
  let y := #f64[1.0, 2.0, 3.0, 4.0, 5.0]
  let n2 := 5
  
  let norm2 := dnrm2 n2 y 0 1
  let dot_self2 := ddot n2 y 0 1 y 0 1
  
  IO.println s!"\nVector: [1.0, 2.0, 3.0, 4.0, 5.0]"
  IO.println s!"Norm: {norm2}"
  IO.println s!"Norm squared: {norm2 * norm2}"
  IO.println s!"Dot with self: {dot_self2}"
  IO.println s!"Difference: {Float.abs (norm2 * norm2 - dot_self2)}"

def test_axpy_linearity : IO Unit := do
  IO.println "\n\nTesting AXPY linearity..."
  
  let x := #f64[1.0, 2.0, 3.0]
  let y := #f64[4.0, 5.0, 6.0]
  let n := 3
  let alpha := 2.0
  let beta := 3.0
  
  -- Test: (alpha + beta) * x + y should equal alpha * x + y + beta * x
  -- But axpy computes: y := alpha * x + y, modifying y in place
  
  -- Method 1: (alpha + beta) * x + y
  let y_copy1 := dcopy n y 0 1 (#f64[0.0, 0.0, 0.0]) 0 1
  let result1 := daxpy n (alpha + beta) x 0 1 y_copy1 0 1
  
  -- Method 2: alpha * x + (beta * x + y)
  let y_copy2 := dcopy n y 0 1 (#f64[0.0, 0.0, 0.0]) 0 1
  let temp := daxpy n beta x 0 1 y_copy2 0 1
  let result2 := daxpy n alpha x 0 1 temp 0 1
  
  IO.println s!"x = {x.toFloatArray}"
  IO.println s!"y = {y.toFloatArray}"
  IO.println s!"alpha = {alpha}, beta = {beta}"
  IO.println s!"(alpha + beta) * x + y = {result1.toFloatArray}"
  IO.println s!"alpha * x + (beta * x + y) = {result2.toFloatArray}"
  
  -- Check if they're equal
  let diff := daxpy n (-1.0) result1 0 1 result2 0 1
  let norm_diff := dnrm2 n diff 0 1
  IO.println s!"Norm of difference: {norm_diff}"

def main : IO Unit := do
  test_norm_squared
  test_axpy_linearity