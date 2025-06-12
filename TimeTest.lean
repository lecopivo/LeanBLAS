import LeanBLAS
import LeanBLAS.FFI
import LeanBLAS.CBLAS.LevelOne

open BLAS CBLAS

/--
Quick timing helper to sanity-check whether the FFI `ddot` call really runs the
full computation.  We compare the latency of a *single* call with the average
latency of multiple calls.  If the compiler accidentally optimized the loop
away, the second measurement would be unrealistically small.
-/
def main : IO Unit := do
  let size := 1000000
  let mut arr := FloatArray.emptyWithCapacity size
  for i in [:size] do
    arr := arr.push (Float.ofNat (i + 1))
  let x := arr.toFloat64Array
  let y := x

  -- Single call ------------------------------------------------------------
  let start1 ← IO.monoNanosNow
  let r := ddot size x 0 1 y 0 1
  let end1 ← IO.monoNanosNow
  let time_single := Float.ofNat (end1 - start1) / 1e9
  IO.println s!"Single call result: {r}, time: {time_single}s"

  -- Ten calls --------------------------------------------------------------
  let iterations := 10
  let mut checksum : Float := 0.0
  let start2 ← IO.monoNanosNow
  for i in [:iterations] do
    let n_i := size - i
    checksum := checksum + ddot n_i x i.toUSize 1 y i.toUSize 1
  let end2 ← IO.monoNanosNow
  IO.println s!"nanos start2 {start2} end2 {end2} diff {end2 - start2}"
  let time_total := Float.ofNat (end2 - start2) / 1e9
  IO.println s!"Checksum: {checksum}"
  IO.println s!"Average time over {iterations} calls: {time_total / Float.ofNat iterations}s"

  pure ()
