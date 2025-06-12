import LeanBLAS

/-!
# Performance Benchmarking Suite for LeanBLAS

This module provides comprehensive performance benchmarking that compares
LeanBLAS operations against theoretical complexity bounds and reference
implementations.
-/

open BLAS CBLAS

namespace BLAS.Test.Benchmarks

/-- Timer utility for measuring execution time -/
structure Timer where
  start_time : UInt64    -- nanoseconds since arbitrary epoch

namespace Timer

def start : IO Timer := do
  let t ← IO.monoNanosNow
  return { start_time := t }

def elapsed (timer : Timer) : IO Float := do
  let t ← IO.monoNanosNow
  let diff : UInt64 := t - timer.start_time
  return Float.ofNat diff.toNat / 1000000000.0

def elapsedNs (timer : Timer) : IO UInt64 := do
  let t ← IO.monoNanosNow
  pure (t - timer.start_time)

/-- Pretty-print a duration given in seconds, automatically switching units so
small values (< 1 µs) remain visible. -/
def formatTime (sec : Float) : String :=
  if sec ≥ 0.001 then s!"{Float.toString sec} s"
  else if sec ≥ 1e-6 then s!"{Float.toString (sec * 1e6)} µs"
  else s!"{Float.toString (sec * 1e9)} ns"

end Timer

-- namespace-level re-export so callers can use `Timer.formatTime` or
-- `Benchmarks.formatTime` interchangeably.
namespace Timer

def formatTime (sec : Float) : String :=
  _root_.BLAS.Test.Benchmarks.formatTime sec

end Timer

/-- Generate a test vector of given size with known pattern -/
def generateTestVector (size : Nat) : Float64Array := Id.run do
  let mut arr := FloatArray.emptyWithCapacity size
  for i in [:size] do
    arr := arr.push (Float.sin (Float.ofNat i * 0.1))
  arr.toFloat64Array

/-- Benchmark dot product operation -/
def benchmarkDot (sizes : List Nat) : IO Unit := do
  IO.println "Benchmarking DOT product operation"
  IO.println (String.mk (List.replicate 40 '-'))
  IO.println "Size\t\tTime (s)\tGFLOPS\t\tOps/sec"

  for size in sizes do
    let x := generateTestVector size
    let y := generateTestVector size

    -- Warm up
    for _ in [:10] do
      let _ := ddot size x 0 1 y 0 1

    -- Benchmark
    let iterations := if size > 1000000 then 10 else if size > 100000 then 50 else if size > 10000 then 100 else 500
    let timer ← Timer.start
    let mut checksum : Float := 0.0
    for i in [:iterations] do
      let n_i := size - i
      checksum := checksum + ddot n_i.toUSize x i.toUSize 1 y i.toUSize 1
    let elapsed ← timer.elapsed

    let time_per_op := elapsed / Float.ofNat iterations
    let flops := Float.ofNat (2 * size)  -- 2 operations per element (multiply + add)
    let gflops := flops / (time_per_op * 1e9)
    let ops_per_sec := 1.0 / time_per_op

    IO.println s!"{size}\t\t{Timer.formatTime time_per_op}\t{Float.toString gflops}\t\t{Float.toString ops_per_sec}\tchk:{checksum}"

/-- Benchmark norm computation -/
def benchmarkNorm (sizes : List Nat) : IO Unit := do
  IO.println "\nBenchmarking NORM computation"
  IO.println (String.mk (List.replicate 40 '-'))
  IO.println "Size\t\tTime (s)\tGFLOPS\t\tOps/sec"

  for size in sizes do
    let x := generateTestVector size

    -- Warm up
    for _ in [:10] do
      let _ := dnrm2 size x 0 1

    -- Benchmark
    let iterations := if size > 1000000 then 10 else if size > 100000 then 50 else if size > 10000 then 100 else 500
    let timer ← Timer.start
    let mut checksum : Float := 0.0
    for i in [:iterations] do
      let n_i := size - i
      checksum := checksum + dnrm2 n_i.toUSize x i.toUSize 1
    let elapsed ← timer.elapsed

    let time_per_op := elapsed / Float.ofNat iterations
    let flops := Float.ofNat (2 * size + 1)  -- 2 ops per element + sqrt
    let gflops := flops / (time_per_op * 1e9)
    let ops_per_sec := 1.0 / time_per_op

    IO.println s!"{size}\t\t{Timer.formatTime time_per_op}\t{Float.toString gflops}\t\t{Float.toString ops_per_sec}\tchk:{checksum}"

/-- Benchmark axpy operation -/
def benchmarkAxpy (sizes : List Nat) : IO Unit := do
  IO.println "\nBenchmarking AXPY operation"
  IO.println (String.mk (List.replicate 40 '-'))
  IO.println "Size\t\tTime (s)\tGFLOPS\t\tOps/sec"

  for size in sizes do
    let x := generateTestVector size
    let y := generateTestVector size
    let alpha := 2.5

    -- Warm up
    for _ in [:10] do
      let _ := daxpy size alpha x 0 1 y 0 1

    -- Benchmark
    let iterations := if size > 1000000 then 10 else if size > 100000 then 50 else if size > 10000 then 100 else 500
    let timer ← Timer.start
    let mut checksum : Float := 0.0
    let mut y_mut := y
    for i in [:iterations] do
      let n_i := size - i
      y_mut := daxpy n_i.toUSize alpha x i.toUSize 1 y_mut i.toUSize 1
      checksum := checksum + (y_mut.toFloatArray.get! i)
    let elapsed ← timer.elapsed

    let time_per_op := elapsed / Float.ofNat iterations
    let flops := Float.ofNat (2 * size)  -- 2 operations per element
    let gflops := flops / (time_per_op * 1e9)
    let ops_per_sec := 1.0 / time_per_op

    IO.println s!"{size}\t\t{Timer.formatTime time_per_op}\t{Float.toString gflops}\t\t{Float.toString ops_per_sec}\tchk:{checksum}"

/-- Cache performance analysis -/
def analyzeCachePerformance : IO Unit := do
  IO.println "\nCache Performance Analysis"
  IO.println (String.mk (List.replicate 40 '-'))

  let sizes := [1000, 10000, 100000, 1000000]  -- Different cache levels

  IO.println "Testing stride effects on performance..."
  IO.println "Size\t\tStride 1\tStride 2\tStride 4\tStride 8"

  for size in sizes do
    let x := generateTestVector (size * 8)  -- Large enough for all strides
    let mut times : Array Float := #[]

    for stride in [1, 2, 4, 8] do
      let timer ← Timer.start
      let iterations := 1000
      -- accumulate into checksum to avoid optimisation
      let mut acc : Float := 0.0
      for i in [:iterations] do
        acc := acc + dnrm2 size x (0).toUSize stride.toUSize
      let elapsed ← timer.elapsed
      let avg := elapsed / Float.ofNat iterations
      times := times.push avg

    IO.print s!"{size}\t\t"
    for i in [:times.size] do
      IO.print s!"{Timer.formatTime (times[i]!)}\t"
    IO.println ""

/-- Memory bandwidth estimation -/
def estimateMemoryBandwidth : IO Unit := do
  IO.println "\nMemory Bandwidth Estimation"
  IO.println (String.mk (List.replicate 40 '-'))

  let sizes := [100000, 1000000, 10000000]

  IO.println "Size\t\tTime (s)\tBandwidth (GB/s)"

  for size in sizes do
    let x := generateTestVector size

    let timer ← Timer.start
    let iterations := 1000
    let mut checksum : Float := 0.0
    for _ in [:iterations] do
      checksum := checksum + dsum size x 0 1  -- Simple sum operation (memory bound)
    let elapsed ← timer.elapsed

    let time_per_op := elapsed / Float.ofNat iterations
    let bytes_accessed := Float.ofNat size * 8  -- 8 bytes per Float64
    let bandwidth := bytes_accessed / (time_per_op * 1e9)

    IO.println s!"{size}\t\t{Timer.formatTime time_per_op}\t{Float.toString bandwidth}\tchk:{checksum}"

/-- Scaling analysis -/
def analyzeScaling : IO Unit := do
  IO.println "\nScaling Analysis (Time vs. Problem Size)"
  IO.println (String.mk (List.replicate 40 '-'))

  let base_sizes := [1000, 2000, 4000, 8000, 16000, 32000]

  IO.println "Testing linear scaling of operations..."
  IO.println "Size\t\tDOT Time\tNorm Time\tAXPY Time\tTheoretical"

  let mut base_dot_time : Option Float := none
  let mut base_norm_time : Option Float := none
  let mut base_axpy_time : Option Float := none

  for size in base_sizes do
    let x := generateTestVector size
    let y := generateTestVector size

    -- Measure dot product
    let timer1 ← Timer.start
    for _ in [:100] do
      let _ := ddot size x 0 1 y 0 1
    let dot_time ← timer1.elapsed
    let dot_time_avg := dot_time / 100.0

    -- Measure norm
    let timer2 ← Timer.start
    for _ in [:100] do
      let _ := dnrm2 size x 0 1
    let norm_time ← timer2.elapsed
    let norm_time_avg := norm_time / 100.0

    -- Measure axpy
    let timer3 ← Timer.start
    for _ in [:100] do
      let _ := daxpy size 2.0 x 0 1 y 0 1
    let axpy_time ← timer3.elapsed
    let axpy_time_avg := axpy_time / 100.0

    -- Calculate scaling factors
    let scale_factor := Float.ofNat size / 1000.0
    let theoretical := scale_factor

    if base_dot_time.isNone then
      base_dot_time := some dot_time_avg
      base_norm_time := some norm_time_avg
      base_axpy_time := some axpy_time_avg

    let dot_scale := dot_time_avg / base_dot_time.get!
    let norm_scale := norm_time_avg / base_norm_time.get!
    let axpy_scale := axpy_time_avg / base_axpy_time.get!

    IO.println s!"{size}\t\t{Float.toString dot_scale}\t\t{Float.toString norm_scale}\t\t{Float.toString axpy_scale}\t\t{Float.toString theoretical}"

/-- Main benchmark runner -/
def benchmarksMain : IO Unit := do
  IO.println "LeanBLAS Performance Benchmarking Suite"
  IO.println (String.mk (List.replicate 50 '='))

  -- Use larger sizes for more accurate timing
  let test_sizes := [10000, 100000, 1000000, 5000000]

  benchmarkDot test_sizes
  benchmarkNorm test_sizes
  benchmarkAxpy test_sizes

  analyzeCachePerformance
  estimateMemoryBandwidth
  analyzeScaling

  IO.println "\n✓ Benchmark suite completed!"
  IO.println "\nNote: Performance results depend on:"
  IO.println "- CPU architecture and frequency"
  IO.println "- Memory hierarchy (L1/L2/L3 cache sizes)"
  IO.println "- System load and other running processes"
  IO.println "- Compiler optimizations enabled"

end BLAS.Test.Benchmarks

/-! Entry point for `lake exe BenchmarkTests` -/

def main : IO Unit := BLAS.Test.Benchmarks.benchmarksMain
