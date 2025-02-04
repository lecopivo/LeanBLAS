import LeanBLAS

open BLAS Sorry

def u : DenseVector FloatArray (.subvector (offset := 4) (inc := 3)) 10 Float :=
  DenseVector.ofFn (fun i => i.1.toFloat)

def A : DenseMatrix FloatArray .RowMajor .normal 3 3 Float :=
  DenseMatrix.ofFn (fun i j => i.1.toFloat + 100 * j.1.toFloat)

unsafe def main : IO Unit := do

  IO.println s!"u = {u}"

  IO.println s!"u.asum = {u.asum}"
  IO.println s!"u.nrm2 = {u.nrm2}"
  IO.println s!"u.iamax = {u.iamax}"

  IO.println s!"u.axpy 1 u = {u.axpy 1 u}"
  IO.println s!"u.scal (-2) = {u |>.scal (-2)}"

  IO.println s!""
  IO.println s!"{A}"
  IO.println s!""
  IO.println s!"{A.row' 2}"
  IO.println s!"{(A.row' 2).sum}"
  IO.println s!""
  IO.println s!"{A.col' 2}"
  IO.println s!"{(A.col' 2).sum}"


  let a : DenseVector FloatArray .normal 3 Float := ⟨⟨#[1,2,(← IO.rand 0 100).toFloat]⟩,sorry_proof⟩
  let b : DenseVector FloatArray .normal 3 Float := ⟨⟨#[4,5,(← IO.rand 0 100).toFloat]⟩,sorry_proof⟩

  IO.println s!"a address: {ptrAddrUnsafe a}"
  IO.println s!"b address: {ptrAddrUnsafe b}"

  let c := DenseVector.mul a b
  IO.println s!"c address: {ptrAddrUnsafe c}"
  -- IO.println s!"a = {a}"
  IO.println s!"b = {b}"
