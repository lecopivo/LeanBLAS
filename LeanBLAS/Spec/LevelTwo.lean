namespace BLAS

-- move this to Spec directory
inductive Order where
  | RowMajor
  | ColMajor

-- move this to Spec directory
inductive Transpose where
  | NoTrans
  | Trans
  | ConjTrans

-- move this to Spec directory
inductive UpLo where
  /-- Upper triangular matrix --/
  | Upper
  /-- Lower triangular matrix --/
  | Lower

inductive Diag where
  /-- Non-unit triangular matrix --/
  | NonUnit
  /-- Unit triangular matrix --/
  | Unit
