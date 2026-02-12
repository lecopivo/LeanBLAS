import LeanBLAS

open BLAS CBLAS Sorry

def approxEq (x y : Float) : Bool :=
  (x - y).abs < 1e-14

instance : ToString Float64Array := ⟨fun x => toString (x.toFloatArray)⟩
instance : BEq Float64Array :=
  ⟨fun x y => ((x.toFloatArray).1.zip (y.toFloatArray).1).all (fun (a,b) => a == b)⟩

def test_dgemv : IO Unit := do
  let A := #f64[1.0, 2.0,
                3.0, 4.0]
  let x := #f64[1.0, 1.0]
  let y := #f64[0.0, 0.0]
  -- y = 1.0 * A * x + 0.0 * y
  let y' := dgemv Order.RowMajor.toUInt8 Transpose.NoTrans.toUInt8 2 2 1.0 A 0 2 x 0 1 0.0 y 0 1
  let expected := #f64[3.0, 7.0]
  IO.println s!"dgemv 2 2 1.0 {A} 2 {x} 1 0.0 {y} 1"
  IO.println s!"{y'} == {expected} = {y' == expected}"
  if y' != expected then
    throw $ IO.userError "test_dgemv failed"

/--
info: dgemv 2 2 1.0 [1.000000, 2.000000, 3.000000, 4.000000] 2 [1.000000, 1.000000] 1 0.0 [0.000000, 0.000000] 1
[3.000000, 7.000000] == [3.000000, 7.000000] = true
-/
#guard_msgs in
#eval test_dgemv

def test_dgemv_3_2 : IO Unit := do
  let A := #f64[1.0, 2.0,
                3.0, 4.0,
                5.0, 6.0]
  let x := #f64[1.0, 2.0]
  let y := #f64[0.0, 0.0, 0.0]
  -- y = 1.0 * A * x + 0.0 * y
  -- A is 3x2
  -- [1*1 + 2*2, 3*1+4*2, 5*1+6*2] = [5, 11, 17]
  let y' := dgemv Order.RowMajor.toUInt8 Transpose.NoTrans.toUInt8 3 2 1.0 A 0 2 x 0 1 0.0 y 0 1
  let expected := #f64[5.0, 11.0, 17.0]
  IO.println s!"dgemv 3 2 1.0 {A} 2 {x} 1 0.0 {y} 1"
  IO.println s!"{y'} == {expected} = {y' == expected}"
  if y' != expected then
    throw $ IO.userError "test_dgemv_3_2 failed"

/--
info: dgemv 3 2 1.0 [1.000000, 2.000000, 3.000000, 4.000000, 5.000000, 6.000000] 2 [1.000000, 2.000000] 1 0.0 [0.000000, 0.000000, 0.000000] 1
[5.000000, 11.000000, 17.000000] == [5.000000, 11.000000, 17.000000] = true
-/
#guard_msgs in
#eval test_dgemv_3_2

def test_dgemv_v2 : IO Unit := do
  -- matrix A: [*, 1, 2, *, 3, 4] (lda=3, offA=1, M=2, N=2)
  let A := #f64[0.0, 1.0, 2.0,
                0.0, 3.0, 4.0]
  -- vector x: [*, 1, *, 1, *] (offX=1, incX=2, N=2)
  let x := #f64[0.0, 1.0, 0.0, 1.0, 0.0]
  -- vector y: [*, 0, 0] (offY=1, incY=1, M=2)
  let y := #f64[0.0, 0.0, 0.0]
  -- y = 1.0 * A * x + 0.0 * y
  let y' := dgemv Order.RowMajor.toUInt8 Transpose.NoTrans.toUInt8 2 2 1.0 A 1 3 x 1 2 0.0 y 1 1
  let expected := #f64[0.0, 3.0, 7.0]
  IO.println s!"dgemv_v2: {y'} == {expected} = {y' == expected}"
  if y' != expected then
    throw $ IO.userError "test_dgemv_v2 failed"

/--
info: dgemv_v2: [0.000000, 3.000000, 7.000000] == [0.000000, 3.000000, 7.000000] = true
-/
#guard_msgs in
#eval test_dgemv_v2

def test_dger : IO Unit := do
  let A := #f64[1.0, 2.0,
                3.0, 4.0,
                5.0, 6.0]
  let x := #f64[1.0, 2.0, 3.0]
  let y := #f64[4.0, 5.0]
  -- A is 3x2, RowMajor
  -- A = 1.0 * x * y^T + A
  -- x * y^T = [1*4, 1*5; 2*4, 2*5; 3*4, 3*5] = [4, 5; 8, 10; 12, 15]
  -- A_new = [1+4, 2+5; 3+8, 4+10; 5+12, 6+15] = [5, 7, 11, 14, 17, 21]
  let A' := dger Order.RowMajor.toUInt8 3 2 1.0 x 0 1 y 0 1 A 0 2
  let expected := #f64[5.0, 7.0, 11.0, 14.0, 17.0, 21.0]
  IO.println s!"dger 3 2 1.0 {x} 1 {y} 1 {A} 2"
  IO.println s!"{A'} == {expected} = {A' == expected}"
  if A' != expected then
    throw $ IO.userError "test_dger failed"

/--
info: dger 3 2 1.0 [1.000000, 2.000000, 3.000000] 1 [4.000000, 5.000000] 1 [1.000000, 2.000000, 3.000000, 4.000000, 5.000000, 6.000000] 2
[5.000000, 7.000000, 11.000000, 14.000000, 17.000000, 21.000000] == [5.000000, 7.000000, 11.000000, 14.000000, 17.000000, 21.000000] = true
-/
#guard_msgs in
#eval test_dger

def test_dger_v2 : IO Unit := do
  -- matrix A: [*, 1, 2, *, 3, 4] (lda=3, offA=1, M=2, N=2)
  let A := #f64[0.0, 1.0, 2.0,
                0.0, 3.0, 4.0]
  -- x: [*, 1, 2] (offX=1, incX=1, M=2)
  let x := #f64[0.0, 1.0, 2.0]
  -- y: [*, 1, *, 3, *] (offY=1, incY=2, N=2)
  let y := #f64[0.0, 1.0, 0.0, 3.0, 0.0]
  -- A = 1.0 * x * y^T + A
  -- x * y^T = [1, 3; 2, 6]
  -- A_new = [*, 1+1, 2+3, *, 3+2, 4+6] = [0.0, 2.0, 5.0, 0.0, 5.0, 10.0]
  let A' := dger Order.RowMajor.toUInt8 2 2 1.0 x 1 1 y 1 2 A 1 3
  let expected := #f64[0.0, 2.0, 5.0,
                       0.0, 5.0, 10.0]
  IO.println s!"dger_v2: {A'} == {expected} = {A' == expected}"
  if A' != expected then
    throw $ IO.userError "test_dger_v2 failed"

/--
info: dger_v2: [0.000000, 2.000000, 5.000000, 0.000000, 5.000000, 10.000000] == [0.000000, 2.000000, 5.000000, 0.000000, 5.000000, 10.000000] = true
-/
#guard_msgs in
#eval test_dger_v2

def test_dgbmv : IO Unit := do
  -- 3x3 matrix with 1 sub and 1 super diagonal
  -- A = [1 2 0
  --      3 4 5
  --      0 6 7]
  -- RowMajor Band storage (KL=1, KU=1, lda=3):
  -- Row 0: [*, 1, 2]
  -- Row 1: [3, 4, 5]
  -- Row 2: [6, 7, *]
  let A := #f64[0.0, 1.0, 2.0,
                3.0, 4.0, 5.0,
                6.0, 7.0, 0.0]
  let x := #f64[1.0, 2.0, 3.0]
  let y := #f64[0.0, 0.0, 0.0]
  -- y = 1.0 * A * x + 0.0 * y
  -- y[0] = 1*1 + 2*2 = 5
  -- y[1] = 3*1 + 4*2 + 5*3 = 3 + 8 + 15 = 26
  -- y[2] = 6*2 + 7*3 = 12 + 21 = 33
  let y' := dbmv Order.RowMajor.toUInt8 Transpose.NoTrans.toUInt8 3 3 1 1 1.0 A 0 3 x 0 1 0.0 y 0 1
  let expected := #f64[5.0, 26.0, 33.0]
  IO.println s!"dgbmv: {y'} == {expected} = {y' == expected}"
  if y' != expected then
    throw $ IO.userError "test_dgbmv failed"

/--
info: dgbmv: [5.000000, 26.000000, 33.000000] == [5.000000, 26.000000, 33.000000] = true
-/
#guard_msgs in
#eval test_dgbmv

def test_dtbmv : IO Unit := do
  -- 3x3 upper triangular band matrix with 1 super diagonal
  -- A = [1 2 0
  --      0 3 4
  --      0 0 5]
  -- RowMajor Band storage (K=1, lda=2):
  -- Row 0: [1, 2]
  -- Row 1: [3, 4]
  -- Row 2: [5, *]
  let A := #f64[1.0, 2.0,
                3.0, 4.0,
                5.0, 0.0]
  let x := #f64[1.0, 1.0, 1.0]
  -- x = A * x
  -- x[0] = 1*1 + 2*1 = 3
  -- x[1] = 3*1 + 4*1 = 7
  -- x[2] = 5*1 = 5
  let x' := dtbmv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 3 1 A 0 2 x 0 1
  let expected := #f64[3.0, 7.0, 5.0]
  IO.println s!"dtbmv: {x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtbmv failed"

/--
info: dtbmv: [3.000000, 7.000000, 5.000000] == [3.000000, 7.000000, 5.000000] = true
-/
#guard_msgs in
#eval test_dtbmv

def test_dtpmv : IO Unit := do
  -- 3x3 upper triangular matrix
  -- A = [1 2 3
  --      0 4 5
  --      0 0 6]
  -- RowMajor Packed storage: [1, 2, 3, 4, 5, 6]
  let A := #f64[1.0, 2.0, 3.0, 4.0, 5.0, 6.0]
  let x := #f64[1.0, 1.0, 1.0]
  -- x = A * x
  -- x[0] = 1*1 + 2*1 + 3*1 = 6
  -- x[1] = 4*1 + 5*1 = 9
  -- x[2] = 6*1 = 6
  let x' := dtpmv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 3 A 0 x 0 1
  let expected := #f64[6.0, 9.0, 6.0]
  IO.println s!"dtpmv: {x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtpmv failed"

/--
info: dtpmv: [6.000000, 9.000000, 6.000000] == [6.000000, 9.000000, 6.000000] = true
-/
#guard_msgs in
#eval test_dtpmv

def test_dtrsv : IO Unit := do
  -- A = [2 1
  --      0 3]
  let A := #f64[2.0, 1.0,
                0.0, 3.0]
  let b := #f64[3.0, 3.0]
  -- Solve Ax = b => x = [1, 1]
  let x' := dtrsv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 2 A 0 2 b 0 1
  let expected := #f64[1.0, 1.0]
  IO.println s!"dtrsv: {x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtrsv failed"

/--
info: dtrsv: [1.000000, 1.000000] == [1.000000, 1.000000] = true
-/
#guard_msgs in
#eval test_dtrsv

def test_dtbsv : IO Unit := do
  -- 2x2 upper triangular band matrix (K=1, lda=2)
  -- A = [2 1
  --      0 4]
  -- RowMajor Band storage:
  -- Row 0: [2, 1]
  -- Row 1: [4, *]
  let A := #f64[2.0, 1.0,
                4.0, 0.0]
  let b := #f64[3.0, 4.0]
  -- Solve Ax = b =>
  -- 2x0 + 1x1 = 3
  -- 4x1 = 4 => x1 = 1
  -- 2x0 + 1 = 3 => x0 = 1
  let x' := dtbsv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 2 1 A 0 2 b 0 1
  let expected := #f64[1.0, 1.0]
  IO.println s!"dtbsv: {x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtbsv failed"

/--
info: dtbsv: [1.000000, 1.000000] == [1.000000, 1.000000] = true
-/
#guard_msgs in
#eval test_dtbsv

def test_dtpsv : IO Unit := do
  -- 2x2 upper triangular matrix in packed format
  -- A = [2 1
  --      0 4]
  -- RowMajor Packed: [2, 1, 4]
  let A := #f64[2.0, 1.0, 4.0]
  let b := #f64[3.0, 4.0]
  -- Solve Ax = b => x = [1, 1]
  let x' := dtpsv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 2 A 0 b 0 1
  let expected := #f64[1.0, 1.0]
  IO.println s!"dtpsv: {x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtpsv failed"

/--
info: dtpsv: [1.000000, 1.000000] == [1.000000, 1.000000] = true
-/
#guard_msgs in
#eval test_dtpsv

def test_dsyr : IO Unit := do
  let A := #f64[1.0, 2.0,
                2.0, 4.0]
  let x := #f64[1.0, 2.0]
  -- A = 1.0 * x * x^T + A (upper triangle only)
  -- x * x^T = [1.0, 2.0; 2.0, 4.0]
  -- A_new_upper = [1.0+1.0, 2.0+2.0; ?, 4.0+4.0] = [2.0, 4.0; ?, 8.0]
  let A' := dsyr Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 2 1.0 x 0 1 A 0 2
  let expected := #f64[2.0, 4.0,
                       2.0, 8.0]
  IO.println s!"dsyr Order.RowMajor UpLo.Upper 2 1.0 {x} 1 {A} 2"
  IO.println s!"{A'} == {expected} = {A' == expected}"
  if A' != expected then
    throw $ IO.userError "test_dsyr failed"

/--
info: dsyr Order.RowMajor UpLo.Upper 2 1.0 [1.000000, 2.000000] 1 [1.000000, 2.000000, 2.000000, 4.000000] 2
[2.000000, 4.000000, 2.000000, 8.000000] == [2.000000, 4.000000, 2.000000, 8.000000] = true
-/
#guard_msgs in
#eval test_dsyr

def test_dsyr2 : IO Unit := do
  let A := #f64[1.0, 2.0,
                2.0, 4.0]
  let x := #f64[1.0, 0.0]
  let y := #f64[0.0, 1.0]
  -- A = 1.0 * (x*y^T + y*x^T) + A (upper triangle only)
  -- x*y^T = [0 1; 0 0], y*x^T = [0 0; 1 0]
  -- SUM = [0 1; 1 0]
  -- A_new_upper = [1+0, 2+1; ?, 4+0] = [1, 3, ?, 4]
  let A' := dsyr2 Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 2 1.0 x 0 1 y 0 1 A 0 2
  let expected := #f64[1.0, 3.0,
                       2.0, 4.0]
  IO.println s!"dsyr2: {A'} == {expected} = {A' == expected}"
  if A' != expected then
    throw $ IO.userError "test_dsyr2 failed"

/--
info: dsyr2: [1.000000, 3.000000, 2.000000, 4.000000] == [1.000000, 3.000000, 2.000000, 4.000000] = true
-/
#guard_msgs in
#eval test_dsyr2

def test_dtrmv : IO Unit := do
  let A := #f64[1.0, 2.0,
                0.0, 3.0]
  let x := #f64[1.0, 2.0]
  -- x = A * x (upper triangular)
  -- x_new = [1.0*1.0 + 2.0*2.0, 3.0*2.0] = [5.0, 6.0]
  let x' := dtrmv Order.RowMajor.toUInt8 UpLo.Upper.toUInt8 Transpose.NoTrans.toUInt8 0 2 A 0 2 x 0 1
  let expected := #f64[5.0, 6.0]
  IO.println s!"dtrmv Order.RowMajor UpLo.Upper Transpose.NoTrans false 2 {A} 2 {x} 1"
  IO.println s!"{x'} == {expected} = {x' == expected}"
  if x' != expected then
    throw $ IO.userError "test_dtrmv failed"

/--
info: dtrmv Order.RowMajor UpLo.Upper Transpose.NoTrans false 2 [1.000000, 2.000000, 0.000000, 3.000000] 2 [1.000000, 2.000000] 1
[5.000000, 6.000000] == [5.000000, 6.000000] = true
-/
#guard_msgs in
#eval test_dtrmv

def levelTwoTests : IO Unit := do
  test_dgemv
  test_dgemv_3_2
  test_dgemv_v2
  test_dger
  test_dger_v2
  test_dgbmv
  test_dtbmv
  test_dtpmv
  test_dsyr
  test_dsyr2
  test_dtrmv
  test_dtrsv
  test_dtbsv
  test_dtpsv

def main : IO Unit := levelTwoTests
