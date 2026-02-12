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

/--
info: ddot 3 [1.000000, 2.000000, 3.000000] 1 [1.000000, 2.000000, 3.000000] 1
14.000000 == 14.000000 = true
-/
#guard_msgs in
#eval test_ddot

def test_ddot_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0]
  let y := #f64[1.0,2.0,3.0,4.0]
  let r := ddot 3 x 0 2 y 0 3
  let expected := 1.0*1.0 + 3.0*4.0
  IO.println s!"ddot 3 {x} 2 {y} 3"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_ddot_2 failed"

/--
info: ddot 3 [1.000000, 2.000000, 3.000000, 4.000000] 2 [1.000000, 2.000000, 3.000000, 4.000000] 3
13.000000 == 13.000000 = true
-/
#guard_msgs in
#eval test_ddot_2

def test_dnrm2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0]
  let r := dnrm2 3 x 0 1
  let expected := Float.sqrt (1.0*1.0 + 2.0*2.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dnrm2 failed"

/--
info: dnrm2 3 [1.000000, 2.000000, 3.000000] 1
3.741657 == 3.741657 = true
-/
#guard_msgs in
#eval test_dnrm2

def test_dnrm2_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0]
  let r := dnrm2 3 x 0 2
  let expected := Float.sqrt (1.0*1.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dnrm2_2 failed"

/--
info: dnrm2 3 [1.000000, 2.000000, 3.000000] 2
3.162278 == 3.162278 = true
-/
#guard_msgs in
#eval test_dnrm2_2

def test_dasum : IO Unit := do
  let x := #f64[1.0,-2.0,3.0]
  let r := dasum 3 x 0 1
  let expected := 1.0 + 2.0 + 3.0
  IO.println s!"dasum 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dasum failed"

/--
info: dasum 3 [1.000000, -2.000000, 3.000000] 1
6.000000 == 6.000000 = true
-/
#guard_msgs in
#eval test_dasum

def test_dasum_2 : IO Unit := do
  let x := #f64[1.0,-2.0,3.0]
  let r := dasum 3 x 0 2
  let expected := 1.0 + 3.0
  IO.println s!"dasum 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if !(approxEq r expected) then
    throw $ IO.userError "test_dasum_2 failed"

/--
info: dasum 3 [1.000000, -2.000000, 3.000000] 2
4.000000 == 4.000000 = true
-/
#guard_msgs in
#eval test_dasum_2

def test_idamax : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,-10.0]
  let r := idamax 4 x 0 1
  let expected := 3
  IO.println s!"idamax 4 {x} 0 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_idamax failed"

/--
info: idamax 4 [1.000000, -2.000000, 3.000000, -10.000000] 0 1
3 == 3 = true
-/
#guard_msgs in
#eval test_idamax

def test_idamax_2 : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,-10.0]
  let r := idamax 2 x 0 2
  let expected := 1
  IO.println s!"idamax 2 {x} 1 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_idamax_2 failed"

/--
info: idamax 2 [1.000000, -2.000000, 3.000000, -10.000000] 1 2
1 == 1 = true
-/
#guard_msgs in
#eval test_idamax_2

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

/--
info: dswap 3 [1.000000, -2.000000, 3.000000, 4.000000] 1 [-1.000000, 2.000000, -3.000000, -4.000000] 1
[-1.000000, 2.000000, -3.000000, -4.000000] == [-1.000000, 2.000000, -3.000000, -4.000000] = true
[1.000000, -2.000000, 3.000000, 4.000000] == [1.000000, -2.000000, 3.000000, 4.000000] = true
-/
#guard_msgs in
#eval test_dswap

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

/--
info: dswap 3 [1.000000, 2.000000, 3.000000, 4.000000, 5.000000] 2 [-1.000000, -2.000000, -3.000000, -4.000000, -5.000000] 3
[-2.000000, 2.000000, -3.000000, 4.000000, -4.000000] == [-2.000000, 2.000000, -3.000000, 4.000000, -4.000000] = true
[-1.000000, 1.000000, 3.000000, 5.000000, -5.000000] == [-1.000000, 1.000000, 3.000000, 5.000000, -5.000000] = true
-/
#guard_msgs in
#eval test_dswap_2

def test_dcopy : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,4.0]
  let y := #f64[0.0,0.0,0.0,0.0]
  let y' := dcopy 4 x 0 1 y 0 1
  IO.println s!"dcopy 4 {x} 0 1 {y} 0 1"
  IO.println s!"{y'} == {x} = {y' == x}"
  if y' != x then
    throw $ IO.userError "test_dcopy failed"

/--
info: dcopy 4 [1.000000, -2.000000, 3.000000, 4.000000] 0 1 [0.000000, 0.000000, 0.000000, 0.000000] 0 1
[1.000000, -2.000000, 3.000000, 4.000000] == [1.000000, -2.000000, 3.000000, 4.000000] = true
-/
#guard_msgs in
#eval test_dcopy

def test_dcopy_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0,5.0]
  let y := #f64[0.0,0.0,0.0,0.0,0.0]
  let y' := dcopy 3 x 0 2 y 1 1
  let y_expected := #f64[0.0,1.0,3.0,5.0,0.0]
  IO.println s!"dcopy 3 {x} 0 2 {y} 1 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_dcopy_2 failed"

/--
info: dcopy 3 [1.000000, 2.000000, 3.000000, 4.000000, 5.000000] 0 2 [0.000000, 0.000000, 0.000000, 0.000000, 0.000000] 1 1
[0.000000, 1.000000, 3.000000, 5.000000, 0.000000] == [0.000000, 1.000000, 3.000000, 5.000000, 0.000000] = true
-/
#guard_msgs in
#eval test_dcopy_2

def test_daxpy : IO Unit := do
  let x := #f64[1.0,-2.0,3.0,4.0]
  let y := #f64[-1.0,4.0,2.0,1.0]
  let y' := daxpy 4 2.0 x 0 1 y 0 1
  let y_expected := #f64[1.0,0.0,8.0,9.0]
  IO.println s!"daxpy 4 2.0 {x} 0 1 {y} 0 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_daxpy failed"

/--
info: daxpy 4 2.0 [1.000000, -2.000000, 3.000000, 4.000000] 0 1 [-1.000000, 4.000000, 2.000000, 1.000000] 0 1
[1.000000, 0.000000, 8.000000, 9.000000] == [1.000000, 0.000000, 8.000000, 9.000000] = true
-/
#guard_msgs in
#eval test_daxpy

def test_daxpy_2 : IO Unit := do
  let x := #f64[1.0,2.0,3.0,4.0,5.0]
  let y := #f64[5.0,4.0,3.0,2.0,1.0]
  let y' := daxpy 3 2.0 x 0 2 y 1 1
  let y_expected := #f64[5.0,6.0,9.0,12.0,1.0]
  IO.println s!"daxpy 3 2.0 {x} 0 2 {y} 1 1"
  IO.println s!"{y'} == {y_expected} = {y' == y_expected}"
  if y' != y_expected then
    throw $ IO.userError "test_daxpy_2 failed"

/--
info: daxpy 3 2.0 [1.000000, 2.000000, 3.000000, 4.000000, 5.000000] 0 2 [5.000000, 4.000000, 3.000000, 2.000000, 1.000000] 1 1
[5.000000, 6.000000, 9.000000, 12.000000, 1.000000] == [5.000000, 6.000000, 9.000000, 12.000000, 1.000000] = true
-/
#guard_msgs in
#eval test_daxpy_2


def test_dconst : IO Unit := do

  let x_expected := #f64[4.2,4.2,4.2]
  let x := dconst 3 4.2

  IO.println s!"dconst 3 4.2"
  IO.println s!"{x} == {x_expected} = {x == x_expected}"

/--
info: dconst 3 4.2
[4.200000, 4.200000, 4.200000] == [4.200000, 4.200000, 4.200000] = true
-/
#guard_msgs in
#eval test_dconst


def levelOneTests : IO Unit := do
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

def main : IO Unit := levelOneTests
