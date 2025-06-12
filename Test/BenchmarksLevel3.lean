import LeanBLAS
import LeanBLAS.CBLAS.LevelThree
import LeanBLAS.FFI.CBLASLevelThreeFloat64

open BLAS.CBLAS

private def gemmNat (order : BLAS.Order) (transA transB : BLAS.Transpose)
    (M N K : Nat) (alpha : Float) (A : BLAS.Float64Array) (offA lda : Nat)
    (B : BLAS.Float64Array) (offB ldb : Nat) (beta : Float)
    (C : BLAS.Float64Array) (offC ldc : Nat) : BLAS.Float64Array :=
  dgemm order transA transB M.toUSize N.toUSize K.toUSize alpha A offA.toUSize lda.toUSize B offB.toUSize ldb.toUSize beta C offC.toUSize ldc.toUSize

open BLAS CBLAS

namespace BLAS.Test.Level3Benchmarks

/-- Generate a `Float64Array` representing a row-major matrix with dimensions
`rows × cols`.  Entry `(i,j)` = `sin ((i * cols + j) * 0.1)`. -/
def genMat (rows cols : Nat) : BLAS.Float64Array := Id.run do
  let mut arr := FloatArray.emptyWithCapacity (rows * cols)
  for idx in [:rows * cols] do
    arr := arr.push (Float.sin (Float.ofNat idx * 0.1))
  arr.toFloat64Array

/-- Pretty-print seconds with adaptive units (shared with other benchmarks). -/
private def formatTime (sec : Float) : String :=
  if sec ≥ 0.001 then s!"{Float.toString sec} s"
  else if sec ≥ 1e-6 then s!"{Float.toString (sec*1e6)} µs"
  else s!"{Float.toString (sec*1e9)} ns"

/-- Benchmark GEMM for square matrices of various sizes. -/
def benchGemm (sizes : List Nat) : IO Unit := do
  IO.println "GEMM (C = αAB + βC) benchmarks"
  IO.println (String.mk (List.replicate 40 '-'))
  IO.println "Size\tTime/op\tGFLOPS\tchk"

  for n in sizes do
    let m := n; let k := n
    let a := genMat m k
    let b := genMat k n
    let mut c := genMat m n

    -- Warm-up
    let _ := gemmNat Order.RowMajor Transpose.NoTrans Transpose.NoTrans m n k 1.0 a 0 k b 0 n 0.0 c 0 n

    let iterations := (if n ≤ 128 then 50 else if n ≤ 256 then 20 else 5)

    -- Timing loop with checksum accumulation (first element)
    let start ← IO.monoNanosNow
    let mut checksum : Float := 0.0
    for _ in [:iterations] do
      c := gemmNat Order.RowMajor Transpose.NoTrans Transpose.NoTrans m n k 1.0 a 0 k b 0 n 0.0 c 0 n
      checksum := checksum + (c.toFloatArray.get! 0)
    let stop ← IO.monoNanosNow

    let elapsed_sec := Float.ofNat (stop - start) / 1e9
    let time_per_op := elapsed_sec / Float.ofNat iterations

    let flops := 2.0 * (Float.ofNat m) * (Float.ofNat n) * (Float.ofNat k)
    let gflops := flops / (time_per_op * 1e9)

    IO.println s!"{n}x{n}\t{formatTime time_per_op}\t{Float.toString gflops}\t{checksum}"

/-- Small correctness test with 2×2 matrices and known result. -/
def quickCorrectness : IO Unit := do
  IO.println "\nQuick GEMM correctness check (2×2)"
  let a := #f64[1.0, 2.0, 3.0, 4.0] -- row-major 2x2: [[1,2],[3,4]]
  let b := #f64[5.0, 6.0, 7.0, 8.0] -- [[5,6],[7,8]]
  let c := #f64[0.0, 0.0, 0.0, 0.0]
  let res := gemmNat Order.RowMajor Transpose.NoTrans Transpose.NoTrans 2 2 2 1.0 a 0 2 b 0 2 0.0 c 0 2
  let arr := res.toFloatArray
  IO.println s!"Result matrix: {arr}"
  let expected := #[19.0, 22.0, 43.0, 50.0]
  let mut ok := true
  for i in [:arr.size] do
    if Float.abs (arr.get! i - expected[i]!) > 1e-6 then
      ok := false
  if ok then
    IO.println "✓ GEMM correct"
  else
    IO.println "❌ GEMM produced wrong result"

/-- Entry point for `lake exe Level3Benchmarks` -/
def main : IO Unit := do
  quickCorrectness
  IO.println ""
  benchGemm [64, 128, 256, 512]
  IO.println "\n✓ Level-3 benchmarks completed!"

end BLAS.Test.Level3Benchmarks

def main : IO Unit := BLAS.Test.Level3Benchmarks.main
