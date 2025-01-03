import LeanBLAS

open BLAS

def u : DenseVector FloatArray (.subvector (offset := 4) (inc := 3)) 10 Float :=
  DenseVector.ofFn (fun i => i.1.toFloat)


def main : IO Unit := do

  IO.println s!"u = {u}"

  IO.println s!"u.asum = {u.asum}"
  IO.println s!"u.nrm2 = {u.nrm2}"
  IO.println s!"u.iamax = {u.iamax}"

  IO.println s!"u.axpy 1 u = {u.axpy 1 u}"
  IO.println s!"u.scal (-2) = {u|>.scal (-2)}"
