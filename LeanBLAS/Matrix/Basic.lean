import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.CBLAS.LevelOne


namespace BLAS

open LevelOneData LevelTwoData


structure DenseMatrix (Array : Type) (order : Order) {R : Type} (K : Type) (m n : Nat) [Scalar R K] [LevelOneData R K Array]
    where
  data : Array
  h_size : size data = m * n


namespace DenseMatrix

variable
  {Array : Type} {R K : Type} {n m : Nat} {order : Order} [Scalar R R] [Scalar R K] [LevelOne R K Array] [LevelTwoData R K Array]


local notation K "^[" m ", " n "]" => DenseMatrix Array order K m n
local notation K "^[" n "]" => DenseMatrix Array order K n 1

def ofFn (f : Fin m → Fin n → K) : K^[m,n] :=
  let data : Array :=
    match order with
    | .ColMajor =>
      LevelOneData.ofFn fun (idx : Fin (m*n)) =>
        let i : Fin m := ⟨idx.1 % m, sorry⟩
        let j : Fin n := ⟨idx.1 / m, sorry⟩
        f i j
    | .RowMajor =>
      LevelOneData.ofFn fun (idx : Fin (m*n)) =>
        let i : Fin m := ⟨idx.1 / n, sorry⟩
        let j : Fin n := ⟨idx.1 % n, sorry⟩
        f i j
  ⟨data, by cases order <;> simp[data]⟩

def get (x : K^[m,n]) (i : Fin m) (j : Fin n) : K :=
  match order with
  | .ColMajor => LevelOneData.get x.data (i.1+m*j.1)
  | .RowMajor => LevelOneData.get x.data (j.1+n*i.1)

def toString [ToString K] (x : K^[m,n]) : String := Id.run do
  let mut s := "["
  for hi : i in [0:m] do
    let i : Fin m := ⟨i, hi.2⟩
    for hj : j in [0:n] do
      let j : Fin n := ⟨j, hj.2⟩
      s := s ++ ToString.toString (x.get i j)
      if j.1 ≠ n-1 then
        s := s ++ ", "
    if i.1 ≠ m-1 then
      s := s ++ "; "
  s

instance [ToString K] : ToString (K^[m,n]) := ⟨fun x => x.toString⟩

open LevelOneData
unsafe def addImpl (x y : K^[m,n]) : K^[m,n] :=
  let data :=
    if isExclusiveUnsafe x then
      axpy (m*n) 1 y.data 0 1 x.data 0 1
    else
      axpy (m*n) 1 x.data 0 1 y.data 0 1
  ⟨data, by by_cases h : (isExclusiveUnsafe x) <;> simp[h,x.2,y.2,data]⟩

@[implemented_by addImpl]
def add (x y : K^[m,n]) : K^[m,n] := ⟨axpy (m*n) 1 x.data 0 1 y.data 0 1, by simp[y.2]⟩

unsafe def axpyImpl (alpha : K) (x y : K^[m,n]) : K^[m,n] :=
  let data :=
    if isExclusiveUnsafe x then
      axpy (m*n) 1 y.data 0 1 (scal (m*n) alpha x.data 0 1) 0 1
    else
      axpy (m*n) alpha x.data 0 1 y.data 0 1
  ⟨data, by by_cases h : (isExclusiveUnsafe x) <;> simp[h,x.2,y.2,data]⟩

@[implemented_by axpyImpl]
def axpy (alpha : K) (x y : K^[m,n]) : K^[m,n] :=
   ⟨LevelOneData.axpy (m*n) alpha x.data 0 1 y.data 0 1, by simp[y.2]⟩

def sub (x y : K^[m,n]) : K^[m,n] := axpy (-1) y x

def smul (a : K) (x : K^[m,n]) : K^[m,n] := ⟨scal (m*n) a x.data 0 1, by simp[x.2]⟩

def neg (x : K^[m,n]) : K^[m,n] := smul (-1) x

def dot (x y : K^[m,n]) : K := LevelOneData.dot (m*n) x.data 0 1 y.data 0 1

def vecmul (A : K^[m,n]) (x : K^[m]) (y : K^[n]) : K^[n] :=
  let lda :=
    match order with
    | .ColMajor => m
    | .RowMajor => n
  ⟨LevelTwoData.gemv order .NoTrans n m 1 A.data 0 lda x.data 0 1 1 y.data 0 1, sorry⟩


instance : Add (K^[m,n]) := ⟨fun x y => x.add y⟩
instance : Sub (K^[m,n]) := ⟨fun x y => x.sub y⟩
instance : Neg (K^[m,n]) := ⟨fun x => x.neg⟩


end DenseMatrix
