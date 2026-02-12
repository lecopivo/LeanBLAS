import LeanBLAS.FFI.CBLASLevelTwoFloat64
import LeanBLAS.Spec.LevelTwo

namespace BLAS.CBLAS


instance : LevelTwoData Float64Array Float Float where

  gemv order trans M N a A offA ldaA X offX incX b Y offY incY :=
    dgemv order.toUInt8 trans.toUInt8 M.toUSize N.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  bmv order trans M N KL KU a A offA ldaA X offX incX b Y offY incY :=
    dbmv order.toUInt8 trans.toUInt8 M.toUSize N.toUSize KL.toUSize KU.toUSize a
      A offA.toUSize ldaA.toUSize X offX.toUSize incX.toUSize b Y offY.toUSize incY.toUSize

  trmv order uplo trans diag N A offA lda X offX incX :=
    dtrmv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbmv order uplo trans diag N K A offA lda X offX incX :=
    dtbmv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpmv order uplo trans diag N A offA X offX incX :=
    dtpmv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  trsv order uplo trans diag N A offA lda X offX incX :=
    dtrsv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tbsv order uplo trans diag N K A offA lda X offX incX :=
    dtbsv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize K.toUSize A offA.toUSize lda.toUSize X offX.toUSize incX.toUSize

  tpsv order uplo trans diag N A offA X offX incX :=
    dtpsv order.toUInt8 uplo.toUInt8 trans.toUInt8 (if diag then 1 else 0) N.toUSize A offA.toUSize X offX.toUSize incX.toUSize

  ger order M N a X offX incX Y offY incY A offA lda :=
    dger order.toUInt8 M.toUSize N.toUSize a X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize

  her order uplo N alpha X offX incX A offA lda :=
    dsyr order.toUInt8 uplo.toUInt8 N.toUSize alpha X offX.toUSize incX.toUSize A offA.toUSize lda.toUSize

  her2 order uplo N alpha X offX incX Y offY incY A offA lda :=
    dsyr2 order.toUInt8 uplo.toUInt8 N.toUSize alpha X offX.toUSize incX.toUSize Y offY.toUSize incY.toUSize A offA.toUSize lda.toUSize
