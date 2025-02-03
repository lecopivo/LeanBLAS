

namespace BLAS
def Fin.reducelD {α : Type} {n : Nat} (d : α) (f : α → α → α) (g : Fin n → α) : α :=
  if h : n = 0 then d
  else if h : n = 1 then g ⟨0, by omega⟩
  else loop (g ⟨0, by omega⟩) 1
  where
  loop (x : α) (i : Nat) : α :=
    if h : i < n then loop (f x (g ⟨i, h⟩)) (i+1) else x
  termination_by n - i
  decreasing_by decreasing_trivial_pre_omega

axiom silentSorry {P : Prop} : P


scoped macro "sorry_proof" : tactic => `(tactic| exact silentSorry)
scoped macro "sorry_proof" : term => `(silentSorry)
