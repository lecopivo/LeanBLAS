import Lean
import LeanBLAS
import LeanBLAS.FFI
import LeanBLAS.CBLAS.LevelOne
open BLAS CBLAS

def main : IO Unit := do
  let size := 1000000
  let mut arr := FloatArray.emptyWithCapacity size
  for i in [:size] do
    arr := arr.push (Float.ofNat (i + 1))
  let x := arr.toFloat64Array
  let y := x
  let iterations := 10
  let start ← IO.monoNanosNow
  for _ in [:iterations] do
    let _ := ddot size x 0 1 y 0 1
  let finish ← IO.monoNanosNow
  let diff := finish - start
  IO.println s!"Nanos: {diff}"
  let seconds := Float.ofNat diff.toNat / 1e9
  IO.println s!"Seconds: {seconds}"
