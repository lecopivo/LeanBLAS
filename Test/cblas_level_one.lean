import LeanBLAS

open BLAS CBLAS Sorry

def approxEq (x y : Float) : Bool :=
  (x - y).abs < 1e-14


instance : ToString Float64Array := ⟨fun x => toString (x.toFloatArray)⟩
instance : BEq Float64Array :=
  ⟨fun x y => ((x.toFloatArray).1.zip (y.toFloatArray).1).all (fun (a,b) => a == b)⟩


def test_ddot : IO Unit := do
  let x := #f64[1.0,2.0,3.0]
  let y := #f64[1.0,2.0,3.0]
  let r := ddot 3 x 0 1 y 0 1
  let expected := 1.0*1.0 + 2.0*2.0 + 3.0*3.0
  IO.println s!"ddot 3 {x} 1 {y} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_ddot failed"

def test_ddot_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0]
  let y := #f64[1.0,2.0,3.0,4.0]
  let r := ddot 3 x 0 2 y 0 3
  let expected := 1.0*1.0 + 3.0*4.0
  IO.println s!"ddot 3 {x} 2 {y} 3"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_ddot_2 failed"


def test_dnrm2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0]
  let r := dnrm2 3 x 0 1
  let expected := Float.sqrt (1.0*1.0 + 2.0*2.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dnrm2 failed"

def test_dnrm2_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0]
  let r := dnrm2 3 x 0 2
  let expected := Float.sqrt (1.0*1.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dnrm2_2 failed"

def test_dasum : IO Unit := do
  let x := #f64[1.0,-2.0,3.0]
  let r := dasum 3 x 0 1
  let expected := 1.0 + 2.0 + 3.0
  IO.println s!"dasum 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dasum failed"

def test_dasum_2 : IO Unit := do
  let x := #f64[1.0,-2.0,3.0]
  let r := dasum 3 x 0 2
  let expected := 1.0 + 3.0
  IO.println s!"dasum 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dasum_2 failed"

def test_idamax : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,-10.0]
  let r := idamax 4 x 0 1
  let expected := 3
  IO.println s!"idamax 4 {x} 0 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_idamax failed"

def test_idamax_2 : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,-10.0]
  let r := idamax 2 x 0 2
  let expected := 1
  IO.println s!"idamax 2 {x} 1 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_idamax_2 failed"

instance : BEq FloatArray := ⟨fun x y => Id.run do
  if x.size != y.size then
    return false
  let mut i := 0
  while i < x.size do
    if x.data[i]! != y.data[i]! then
      return false
    i := i + 1
  return true⟩

def test_dswap : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,4.0]
  let y := #f64[-1.0,2.0,-3.0,-4.0]
  let (x',y') := dswap 4 x 0 1 y 0 1
  IO.println s!"dswap 3 {x} 1 {y} 1"
  IO.println s!"{x'} == {y} = {x' == y}"
  IO.println s!"{y'} == {x} = {y' == x}"
  if x != y' then
    throw $ IO.userError "test_dswap failed"

def test_dswap_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0,5.0]
  let y := #f64[-1.0,-2.0,-3.0,-4.0,-5.0]
  let (x',y') := dswap 3 x 0 2 y 1 1
  let x'_expected := #f64[-2,2,-3,4,-4]
  let y'_expected := #f64[-1,1,3,5,-5]
  IO.println s!"dswap 3 {x} 2 {y} 3"
  IO.println s!"{x'} == {x'_expected} = {x' == x'_expected}"
  IO.println s!"{y'} == {y'_expected} = {y' == y'_expected}"
  if x' != x'_expected then
    throw $ IO.userError "test_dswap_2 failed"

def test_dcopy : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,4.0]
  let y := #f64[0.0,0.0,0.0,0.0]
  let y' := dcopy 4 x 0 1 y 0 1
  IO.println s!"dcopy 4 {x} 0 1 {y} 0 1"
  IO.println s!"{y'} == {x} = {y' == x}"
  if y' != x then
    throw $ IO.userError "test_dcopy failed"

def test_dcopy_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0,5.0]
  let y := #f64[0.0,0.0,0.0,0.0,0.0]
  let y' := dcopy 3 x 0 2 y 1 1
  let y_expected := #f64[0.0,1.0,3.0,5.0,0.0]
  IO.println s!"dcopy 3 {x} 0 2 {y} 1 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_dcopy_2 failed"

def test_daxpy : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,4.0]
  let y := #f64[-1.0,4.0,2.0,1.0]
  let y' := daxpy 4 2.0 x 0 1 y 0 1
  let y_expected := #f64[1.0,0.0,8.0,9.0]
  IO.println s!"daxpy 4 2.0 {x} 0 1 {y} 0 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_daxpy failed"

def test_daxpy_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0,5.0]
  let y := #f64[5.0,4.0,3.0,2.0,1.0]
  let y' := daxpy 3 2.0 x 0 2 y 1 1
  let y_expected := #f64[5.0,6.0,9.0,12.0,1.0]
  IO.println s!"daxpy 3 2.0 {x} 0 2 {y} 1 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_daxpy_2 failed"


def test_dconst : IO Unit := do

  let x_expected := #f64[4.2,4.2,4.2]
  let x := dconst 3 4.2

  IO.println s!"dconst 3 4.2"
  IO.println s!"{x} == {x_expected} = {x == x_expected}"


def main : IO Unit := do
  test_ddot
  test_ddot_2
  test_dnrm2
  test_dnrm2_2
  test_dasum
  test_dasum_2
  test_idamax
  test_idamax_2
  test_dswap
  test_dswap_2
  test_dcopy
  test_dcopy_2
  test_daxpy
  test_daxpy_2
  test_dconst

#eval main
