import LeanBLAS

/-- Local pretty-printer for durations (replicates logic in Test/Benchmarks) -/
def formatTime (sec : Float) : String :=
  if sec ≥ 0.001 then s!"{Float.toString sec} s"
  else if sec ≥ 1e-6 then s!"{Float.toString (sec * 1e6)} µs"
  else s!"{Float.toString (sec * 1e9)} ns"

open BLAS CBLAS

namespace BLAS.Test.BenchmarksFixed

/-- Approximate equality check for floats -/
def approxEq (x y : Float) (tol : Float := 1e-10) : Bool :=
  (x - y).abs < tol

/-- Generate a test vector with a simple pattern -/
def generateTestVector (size : Nat) : Float64Array := Id.run do
  let mut arr := FloatArray.emptyWithCapacity size
  for i in [:size] do
    arr := arr.push (Float.ofNat (i + 1))  -- Simple 1, 2, 3, ... pattern
  arr.toFloat64Array

/-- Test and benchmark dot product -/
def testDotProduct : IO Unit := do
  IO.println "\n=== DOT Product Test ==="
  
  -- Small test for correctness
  let x_small := #f64[1.0, 2.0, 3.0, 4.0]
  let y_small := #f64[2.0, 3.0, 4.0, 5.0]
  let result_small := ddot 4 x_small 0 1 y_small 0 1
  let expected_small := 1.0*2.0 + 2.0*3.0 + 3.0*4.0 + 4.0*5.0  -- = 40
  IO.println s!"Small test: dot([1,2,3,4], [2,3,4,5]) = {result_small}
Expected: {expected_small}"
  if !approxEq result_small expected_small then
    IO.println "❌ DOT product failed correctness test!"
  else
    IO.println "✓ DOT product correct"
  
  -- Benchmark with larger size
  let size := 1000000
  IO.println s!"\nBenchmarking with size {size}..."
  let x := generateTestVector size
  let y := generateTestVector size
  
  -- Time a single operation first
  let start_single ← IO.monoNanosNow
  let result := ddot size x 0 1 y 0 1
  let end_single ← IO.monoNanosNow
  let single_time := Float.ofNat (end_single - start_single) / 1e9
  IO.println s!"Single operation result: {result}
Single operation time: {single_time} seconds"
  
  -- Now benchmark multiple iterations
  -- We accumulate the results into a dummy variable to make sure the compiler
  -- cannot optimize away the actual BLAS calls.  This also gives us an extra
  -- sanity-check that subsequent iterations keep producing the same number.
  let iterations := 10
  let mut acc : Float := 0.0
  let start ← IO.monoNanosNow
  for i in [:iterations] do
    let n_i := size - i
    acc := acc + ddot n_i.toUSize x i.toUSize 1 y i.toUSize 1
  let end_time ← IO.monoNanosNow

  -- Use the accumulator so the result is observable.
  IO.println s!"Checksum (acc): {acc}"

  let total_time := Float.ofNat (end_time - start) / 1e9
  let time_per_op := total_time / Float.ofNat iterations
  let flops := Float.ofNat (2 * size) -- multiply + add per element
  let gflops := flops / (time_per_op * 1e9)

  IO.println s!"Total time for {iterations} iterations: {total_time} seconds
Time per operation: {formatTime time_per_op}
Performance: {gflops} GFLOPS"

/-- Test and benchmark norm computation -/
def testNorm : IO Unit := do
  IO.println "\n=== NORM (dnrm2) Test ==="
  
  -- Small test for correctness
  let x_small := #f64[3.0, 4.0]  -- Should give norm = 5
  let result_small := dnrm2 2 x_small 0 1
  let expected_small := 5.0
  IO.println s!"Small test: norm([3, 4]) = {result_small}
Expected: {expected_small}"
  if !approxEq result_small expected_small then
    IO.println "❌ NORM failed correctness test!"
  else
    IO.println "✓ NORM correct"
  
  -- Benchmark
  let size := 1000000
  IO.println s!"\nBenchmarking with size {size}..."
  let x := generateTestVector size
  
  let iterations := 10
  let mut acc : Float := 0.0
  let start ← IO.monoNanosNow
  for i in [:iterations] do
    let n_i := size - i
    acc := acc + dnrm2 n_i.toUSize x i.toUSize 1
  let end_time ← IO.monoNanosNow

  let total_time := Float.ofNat (end_time - start) / 1e9
  let time_per_op := total_time / Float.ofNat iterations
  let flops := Float.ofNat (2 * size + 1)  -- square + accumulate + sqrt
  let gflops := flops / (time_per_op * 1e9)

  IO.println s!"Checksum (acc): {acc}"
  IO.println s!"Total time for {iterations} iterations: {total_time} seconds
Time per operation: {formatTime time_per_op}
Performance: {gflops} GFLOPS"

/-- Test and benchmark AXPY operation -/
def testAxpy : IO Unit := do
  IO.println "\n=== AXPY Test ==="
  
  -- Small test for correctness
  let x_small := #f64[1.0, 2.0, 3.0]
  let mut y_small := #f64[4.0, 5.0, 6.0]
  let alpha := 2.0
  y_small := daxpy 3 alpha x_small 0 1 y_small 0 1
  IO.println s!"Small test: y = {alpha} * [1,2,3] + [4,5,6]"
  IO.println s!"Result: {y_small.toFloatArray}"
  let expected := #[6.0, 9.0, 12.0]  -- 2*1+4, 2*2+5, 2*3+6
  let y_arr := y_small.toFloatArray
  let mut allCorrect := y_arr.size == expected.size
  if allCorrect then
    for i in [:y_arr.size] do
      if !approxEq y_arr[i]! expected[i]! then
        allCorrect := false
        break
  if allCorrect then
    IO.println "✓ AXPY correct"
  else
    IO.println "❌ AXPY failed correctness test!"
  
  -- Benchmark
  let size := 1000000
  IO.println s!"\nBenchmarking with size {size}..."
  let x := generateTestVector size
  let mut y := generateTestVector size
  
  let iterations := 10
  let mut checksum := 0.0
  let start ← IO.monoNanosNow
  for i in [:iterations] do
    let n_i := size - i
    y := daxpy n_i.toUSize 2.5 x i.toUSize 1 y i.toUSize 1
    checksum := checksum + (y.toFloatArray.get! i)  -- accumulate varying element
  let end_time ← IO.monoNanosNow

  let total_time := Float.ofNat (end_time - start) / 1e9
  let time_per_op := total_time / Float.ofNat iterations
  let flops := Float.ofNat (2 * size)  -- multiply + add per element
  let gflops := flops / (time_per_op * 1e9)

  IO.println s!"Checksum: {checksum}"
  IO.println s!"Total time for {iterations} iterations: {total_time} seconds
Time per operation: {formatTime time_per_op}
Performance: {gflops} GFLOPS"

/-- Memory bandwidth test -/
def testMemoryBandwidth : IO Unit := do
  IO.println "\n=== Memory Bandwidth Test (using dsum) ==="
  
  let size := 10000000  -- 10 million elements
  IO.println s!"Testing with {size} elements ({Float.ofNat (size * 8) / 1e6} MB)"
  let x := generateTestVector size
  
  -- Warm up
  let _ := dsum size x 0 1
  
  let iterations := 10
  let mut checksum := 0.0
  let start ← IO.monoNanosNow
  for _ in [:iterations] do
    checksum := checksum + dsum size x 0 1
  let end_time ← IO.monoNanosNow

  let total_time := Float.ofNat (end_time - start) / 1e9
  let time_per_op := total_time / Float.ofNat iterations
  let bytes_accessed := Float.ofNat (size * 8)  -- 8 bytes per Float64
  let bandwidth_gb_s := bytes_accessed / (time_per_op * 1e9)

  IO.println s!"Checksum: {checksum}"
  IO.println s!"Time per operation: {formatTime time_per_op}"
  IO.println s!"Memory bandwidth: {bandwidth_gb_s} GB/s"

/-- Main benchmark runner -/
def main : IO Unit := do
  IO.println "LeanBLAS Level 1 Performance Tests"
  IO.println "=================================="
  
  testDotProduct
  testNorm
  testAxpy
  testMemoryBandwidth
  
  IO.println "\n✓ All benchmarks completed!"

end BLAS.Test.BenchmarksFixed

def main : IO Unit := BLAS.Test.BenchmarksFixed.main