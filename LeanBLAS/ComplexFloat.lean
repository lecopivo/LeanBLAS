

namespace BLAS


/-- -/
structure ComplexFloat where
  x : Float
  y : Float
  deriving Inhabited

instance : ToString ComplexFloat where
  toString c := toString c.x ++ " + " ++ toString c.y ++ "ⅈ"

instance : BEq ComplexFloat where
  beq a b := a.x == b.x && a.y == b.y

instance : Add ComplexFloat where
  add a b := ⟨a.x + b.x, a.y + b.y⟩

instance : Sub ComplexFloat where
  sub a b := ⟨a.x - b.x, a.y - b.y⟩

instance : Mul ComplexFloat where
  mul a b := ⟨a.x * b.x - a.y * b.y, a.x * b.y + a.y * b.x⟩

instance : Div ComplexFloat where
  div a b :=
    let d := b.x * b.x + b.y * b.y
    ⟨(a.x * b.x + a.y * b.y) / d, (a.y * b.x - a.x * b.y) / d⟩

instance : HDiv ComplexFloat Float ComplexFloat where
  hDiv a b := ⟨a.x / b, a.y / b⟩

instance : HMul ComplexFloat Float ComplexFloat where
  hMul a b := ⟨a.x * b, a.y * b⟩

instance : HMul Float ComplexFloat ComplexFloat where
  hMul a b := ⟨a * b.x, a * b.y⟩

instance : Neg ComplexFloat where
  neg a := ⟨-a.x, -a.y⟩

def ComplexFloat.zero : ComplexFloat := ⟨0, 0⟩

def ComplexFloat.one : ComplexFloat := ⟨1, 0⟩

def ComplexFloat.I : ComplexFloat := ⟨0, 1⟩

def ComplexFloat.abs (a : ComplexFloat) : Float := Float.sqrt (a.x * a.x + a.y * a.y)

def ComplexFloat.conj (a : ComplexFloat) : ComplexFloat := ⟨a.x, -a.y⟩

def ComplexFloat.exp (a : ComplexFloat) : ComplexFloat :=
  let e := Float.exp a.x
  ⟨e * Float.cos a.y, e * Float.sin a.y⟩

def ComplexFloat.log (a : ComplexFloat) : ComplexFloat :=

  let r := ComplexFloat.abs a
  let θ := Float.atan2 a.y a.x
  ⟨Float.log r, θ⟩

def ComplexFloat.pow (a b : ComplexFloat) : ComplexFloat :=
  ComplexFloat.exp (b * ComplexFloat.log a)

def ComplexFloat.sqrt (a : ComplexFloat) : ComplexFloat :=
  let r := ComplexFloat.abs a
  let θ := Float.atan2 a.y a.x
  let r' := Float.sqrt r
  let θ' := θ / 2
  ⟨r' * Float.cos θ', r' * Float.sin θ'⟩

def ComplexFloat.cbrt (a : ComplexFloat) : ComplexFloat :=
  let r := ComplexFloat.abs a
  let θ := Float.atan2 a.y a.x
  let r' := Float.cbrt r
  let θ' := θ / 3
  ⟨r' * Float.cos θ', r' * Float.sin θ'⟩

def ComplexFloat.sin (a : ComplexFloat) : ComplexFloat :=
  let x := a.x
  let y := a.y
  ⟨Float.sin x * Float.cosh y, Float.cos x * Float.sinh y⟩

def ComplexFloat.cos (a : ComplexFloat) : ComplexFloat :=
  let x := a.x
  let y := a.y
  ⟨Float.cos x * Float.cosh y, -Float.sin x * Float.sinh y⟩

def ComplexFloat.tan (a : ComplexFloat) : ComplexFloat :=
  ComplexFloat.sin a / ComplexFloat.cos a

def ComplexFloat.asin (a : ComplexFloat) : ComplexFloat :=
  -ComplexFloat.log (ComplexFloat.one * ComplexFloat.I - a * ComplexFloat.I) * ComplexFloat.I

def ComplexFloat.acos (a : ComplexFloat) : ComplexFloat :=
  -ComplexFloat.log (a + ComplexFloat.I * ComplexFloat.sqrt (ComplexFloat.one - a * a)) * ComplexFloat.I

def ComplexFloat.atan (a : ComplexFloat) : ComplexFloat :=
  (ComplexFloat.log (ComplexFloat.one - a * ComplexFloat.I) - ComplexFloat.log (ComplexFloat.one + a * ComplexFloat.I)) * ComplexFloat.I / (2.0 : Float)

def ComplexFloat.sinh (a : ComplexFloat) : ComplexFloat :=
  let x := a.x
  let y := a.y
  ⟨Float.sinh x * Float.cos y, Float.cosh x * Float.sin y⟩

def ComplexFloat.cosh (a : ComplexFloat) : ComplexFloat :=
  let x := a.x
  let y := a.y
  ⟨Float.cosh x * Float.cos y, Float.sinh x * Float.sin y⟩

def ComplexFloat.tanh (a : ComplexFloat) : ComplexFloat :=
  ComplexFloat.sinh a / ComplexFloat.cosh a

def ComplexFloat.asinh (a : ComplexFloat) : ComplexFloat :=
  ComplexFloat.log (a + ComplexFloat.sqrt (a * a + ComplexFloat.one))

def ComplexFloat.acosh (a : ComplexFloat) : ComplexFloat :=
  ComplexFloat.log (a + ComplexFloat.sqrt (a * a - ComplexFloat.one))

def ComplexFloat.atanh (a : ComplexFloat) : ComplexFloat :=
  (ComplexFloat.log (ComplexFloat.one + a) - ComplexFloat.log (ComplexFloat.one - a)) / (2.0:Float)


def ComplexFloat.floor (a : ComplexFloat) : ComplexFloat := ⟨Float.floor a.x, Float.floor a.y⟩

def ComplexFloat.ceil (a : ComplexFloat) : ComplexFloat := ⟨Float.ceil a.x, Float.ceil a.y⟩

def ComplexFloat.round (a : ComplexFloat) : ComplexFloat := ⟨Float.round a.x, Float.round a.y⟩

def ComplexFloat.isFinite (a : ComplexFloat) : Bool := a.x.isFinite && a.y.isFinite

def ComplexFloat.isNaN (a : ComplexFloat) : Bool := a.x.isNaN || a.y.isNaN

def ComplexFloat.isInf (a : ComplexFloat) : Bool := a.x.isInf || a.y.isInf


----------------------------------------------------------------------------------------------------


structure ComplexFloatArray where
  data : FloatArray
  deriving Inhabited

def ComplexFloatArray.size (a : ComplexFloatArray) : Nat := a.data.size / 2

def ComplexFloatArray.get! (a : ComplexFloatArray) (i : Nat) : ComplexFloat :=
  ⟨a.data.get! (2*i), a.data.get! (2*i+1)⟩

def ComplexFloatArray.get? (a : ComplexFloatArray) (i : Nat) : Option ComplexFloat :=
  if i < a.size then some (a.get! i)
  else none

def ComplexFloatArray.get (a : ComplexFloatArray) (i : Fin a.size) : ComplexFloat :=
  a.get! i.val

def ComplexFloatArray.set! (a : ComplexFloatArray) (i : Nat) (c : ComplexFloat) : ComplexFloatArray :=
  ⟨a.data.set! (2*i) c.x |>.set! (2*i+1) c.y⟩

def ComplexFloatArray.set (a : ComplexFloatArray) (i : Fin a.size) (c : ComplexFloat) : ComplexFloatArray :=
  a.set! i.val c

def ComplexFloatArray.mkEmpty : ComplexFloatArray := ⟨FloatArray.empty⟩

def ComplexFloatArray.push (a : ComplexFloatArray) (c : ComplexFloat) : ComplexFloatArray :=
  ⟨(a.data.push c.x).push c.y⟩


instance : ToString ComplexFloatArray where
  toString a := Id.run do
    let mut r := "#[" ++ (toString (a.get! 0))
    for i in [1:a.size] do
      r := r ++ ", " ++ toString (a.get! i)
    r := r ++ "]"
    pure r
