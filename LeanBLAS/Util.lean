namespace BLAS

namespace Sorry

axiom silentSorry {P : Prop} : P
scoped macro "sorry_proof" : tactic => `(tactic| exact silentSorry)
scoped macro "sorry_proof" : term => `(silentSorry)
