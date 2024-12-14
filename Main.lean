import LeanBLAS


def test_ddot : IO Unit := do
  let x : FloatArray := ⟨#[1.0,2.0,3.0]⟩
  let y : FloatArray := ⟨#[1.0,2.0,3.0]⟩
  let r := ddot 3 x 0 1 y 0 1
  let expected := 1.0*1.0 + 2.0*2.0 + 3.0*3.0
  IO.println s!"ddot 3 {x} 1 {y} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_ddot failed"

def test_ddot_2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,2.0,3.0,4.0]⟩
  let y : FloatArray := ⟨#[1.0,2.0,3.0,4.0]⟩
  let r := ddot 3 x 0 2 y 0 3
  let expected := 1.0*1.0 + 3.0*4.0
  IO.println s!"ddot 3 {x} 2 {y} 3"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_ddot_2 failed"

def test_dnrm2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,2.0,3.0]⟩
  let r := dnrm2 3 x 0 1
  let expected := Float.sqrt (1.0*1.0 + 2.0*2.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_dnrm2 failed"

def test_dnrm2_2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,2.0,3.0]⟩
  let r := dnrm2 3 x 0 2
  let expected := Float.sqrt (1.0*1.0 + 3.0*3.0)
  IO.println s!"dnrm2 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_dnrm2_2 failed"

def test_dasum : IO Unit := do
  let x : FloatArray := ⟨#[1.0,-2.0,3.0]⟩
  let r := dasum 3 x 0 1
  let expected := 1.0 + 2.0 + 3.0
  IO.println s!"dasum 3 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_dasum failed"

def test_dasum_2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,-2.0,3.0]⟩
  let r := dasum 3 x 0 2
  let expected := 1.0 + 3.0
  IO.println s!"dasum 3 {x} 2"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_dasum_2 failed"

def test_idamax : IO Unit := do
  let x : FloatArray := ⟨#[1.0,-2.0,3.0,-10.0]⟩
  let r := idamax 4 x 0 1
  let expected := 3
  IO.println s!"idamax 4 {x} 1"
  IO.println s!"{r} == {expected} = {r == expected}"
  if r != expected then
    throw $ IO.userError "test_idamax failed"

def test_idamax_2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,-2.0,3.0,-10.0]⟩
  let r := idamax 4 x 0 2
  let expected := 2
  IO.println s!"idamax 4 {x} 2"
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
  let x : FloatArray := ⟨#[1.0,-2.0,3.0,4.0]⟩
  let y : FloatArray := ⟨#[-1.0,2.0,-3.0,-4.0]⟩
  let (x',y') := dswap 4 x 0 1 y 0 1
  IO.println s!"dswap 3 {x} 1 {y} 1"
  IO.println s!"{x} == {y'} = {x == y'}"
  IO.println s!"{y} == {x'} = {y == x'}"
  if x != y' then
    throw $ IO.userError "test_dswap failed"

def test_dswap_2 : IO Unit := do
  let x : FloatArray := ⟨#[1.0,2.0,3.0,4.0,5.0]⟩
  let y : FloatArray := ⟨#[-1.0,-2.0,-3.0,-4.0,-5.0]⟩
  let (x',y') := dswap 3 x 0 2 y 1 1
  let x'_expected : FloatArray := ⟨#[-2,2,-3,4,-4]⟩
  let y'_expected : FloatArray := ⟨#[-1,1,3,5,-5]⟩
  IO.println s!"dswap 3 {x} 2 {y} 3"
  IO.println s!"{x'} == {x'_expected} = {x' == x'_expected}"
  IO.println s!"{y'} == {y'_expected} = {y' == y'_expected}"
  if x' != x'_expected then
    throw $ IO.userError "test_dswap_2 failed"

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
