import LeanBLAS

open BLAS BLAS.Sorry


def approxEq (x y : Float) : Bool :=
  (x - y).abs < 1e-14

def _root_.FloatArray.approxEq (x y : FloatArray) : Bool := Id.run do
  if x.size != y.size then
    return false
  let mut s : Float := 0.0
  for xi in x.data, yi in y.data do
    s := max s (xi-yi).abs
  return s < 1e-14



def main : IO Unit := do

  let n := 4

  -- strict triangular 4×4 matrix
  let Ap : DenseVector FloatArray .normal (n*(n-1)/2) Float :=
    ⟨⟨#[1,2,3,4,5,6]⟩,by simp[DenseVector.Storage.IsValid,LevelOneData.size,n]; sorry_proof⟩

  -- length 4 vector that is a subvector of vector of length 8
  let x : DenseVector FloatArray (.subvector 1 2) n Float :=
    ⟨⟨#[-1,1,-2,10,-3,100,-4,1000]⟩, sorry_proof⟩

  let y := Ap.strictTriangularMul x (ord := .ColMajor) (uplo := .Lower) (trans := .NoTrans)
  IO.println y.data
  if !(y.data.approxEq ⟨#[-1,0,-2,1,-3,42,-4,653]⟩) then
    throw $ IO.userError "test `strictTriangularMul .ColMajor .Lower` failed"

  let y := Ap.strictTriangularMul x (ord := .RowMajor) (uplo := .Lower) (trans := .NoTrans)
  IO.println y.data
  if !(y.data.approxEq ⟨#[-1,0,-2,1,-3,32,-4,654]⟩) then
    throw $ IO.userError "test `strictTriangularMul .Rowmajor .Lower` failed"


  let y := Ap.strictTriangularMul x (ord := .ColMajor) (uplo := .Upper) (trans := .NoTrans)
  IO.println y.data
  if !(y.data.approxEq ⟨#[-1,4210,-2,5300,-3,6000,-4,0]⟩) then
    throw $ IO.userError "test `strictTriangularMul .ColMajor .Lower` failed"

  let y := Ap.strictTriangularMul x (ord := .RowMajor) (uplo := .Upper) (trans := .NoTrans)
  IO.println y.data
  if !(y.data.approxEq ⟨#[-1,3210,-2,5400,-3,6000,-4,0]⟩) then
    throw $ IO.userError "test `strictTriangularMul .Rowmajor .Lower` failed"

  let y := Ap.strictTriangularMul x (ord := .ColMajor) (uplo := .Upper) (trans := .Trans)
  IO.println y.data
  if !(y.data.approxEq ⟨#[-1,0,-2,1,-3,32,-4,654]⟩) then
    throw $ IO.userError "test `strictTriangularMul .ColMajor .Lower` failed"


#eval main
#exit
  let u : FloatArray := ⟨#[10,10,10]⟩
  let v : FloatArray := ⟨#[0,10,0]⟩

  let A' := BLAS.CBLAS.dgpr .ColMajor .Lower 3 1.0 v 0 1 u 0 1 A 0
  IO.println A'

  let B := CBLAS.dpackedToDense 3 .Lower .RowMajor A .ColMajor ⟨Array.mkArray 9 0⟩ 0 3
  IO.println B

  let B := CBLAS.dpackedToDense 3 .Lower .ColMajor A .ColMajor ⟨Array.mkArray 16 0⟩ 1 4
  IO.println B

  let C : FloatArray := ⟨#[1,2,3,4,5,6,7,8,9]⟩
  let Cp := CBLAS.ddenseToPacked 3 .Lower .RowMajor C 0 3 .ColMajor ⟨Array.mkArray 6 0⟩
  IO.println Cp
