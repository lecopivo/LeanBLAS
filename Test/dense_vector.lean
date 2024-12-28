import LeanBLAS

open BLAS


#check DenseVector

def u : DenseVector FloatArray {offset := 4, inc := 3} 10 Float :=
  DenseVector.ofFn (fun i => i.1.toFloat)


def main : IO Unit := do

  IO.println s!"u = {u}"

  IO.println s!"u.asum = {u.asum}"
  IO.println s!"u.nrm2 = {u.nrm2}"
  IO.println s!"u.iamax = {u.iamax}"

  IO.println s!"u.axpy 1 u = {u.axpy 1 u}"
  IO.println s!"u.scal (-2) = {u|>.reinterpret {offset := 7, inc := 6} 4 (by decide)
                                |>.scal (-2)
                                |>.reinterpret {offset := 4, inc := 3} 10 (by sorry)}"
