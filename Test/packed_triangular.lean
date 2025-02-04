import LeanBLAS

open BLAS BLAS.Sorry

def strictLowerTriangularMatMul (A : FloatArray) (x : FloatArray) : FloatArray := Id.run do

  let n := x.size
  if A.size ≠ (n*(n-1))/2 then
    panic! s!"strictLowerTriangularMatMul: invalid size of `A` array, \
              size {A.size} but {(n*(n-1))/2} is expected"
  else
    -- UpLo → Transpose → Bool → Nat → ?m.287 → Nat → ?m.287 → Nat → Nat → ?m.287
    let mut x := LevelTwoData.tpmv .ColMajor .Lower .NoTrans false (n-1) A 0 x 0 1

    -- shift all valus down
    let mut xi := 0
    let mut xi' := 0
    for h : i in [0:x.size] do
      have : i < x.size := sorry_proof
      xi' := x[i] -- store old value
      x := x.set i xi sorry_proof
      xi := xi'
    x

def strictUpperTriangularMatMul (A : FloatArray) (x : FloatArray) : FloatArray := Id.run do

  let n := x.size
  if A.size ≠ (n*(n-1))/2 then
    panic! s!"strictLowerTriangularMatMul: invalid size of `A` array, \
              size {A.size} but {(n*(n-1))/2} is expected"
  else
    -- UpLo → Transpose → Bool → Nat → ?m.287 → Nat → ?m.287 → Nat → Nat → ?m.287
    let mut x := LevelTwoData.tpmv .ColMajor .Upper .NoTrans false (n-1) A 0 x 1 1

    -- shift all valus down
    let mut xi := 0
    let mut xi' := 0
    for h : i in [0:x.size-1] do
      have : i+1 < x.size := sorry_proof
      x := x.set i x[i+1]
    x := x.set (x.size-1) 0 sorry_proof
    x



def main : IO Unit := do

  -- vector for strict lower triangular matrix
  let A : FloatArray := ⟨#[1,2,3,4,5,6]⟩
  let x : FloatArray := ⟨#[1,10,100,1000]⟩

  let Ax := strictLowerTriangularMatMul A x
  IO.println Ax
  let Ax := strictUpperTriangularMatMul A x
  IO.println Ax

  let u : FloatArray := ⟨#[10,10,10]⟩
  let v : FloatArray := ⟨#[0,10,0]⟩

  let A' := BLAS.CBLAS.dgpr .ColMajor .Lower 3 1.0 v 0 1 u 0 1 A 0
  IO.println A'
