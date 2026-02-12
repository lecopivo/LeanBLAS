import LeanBLAS.Spec.LevelOne
import LeanBLAS.Spec.LevelTwo
import LeanBLAS.Spec.LevelThree
import LeanBLAS.CBLAS.LevelOne
import LeanBLAS.CBLAS.LevelTwo
import LeanBLAS.CBLAS.LevelThree

open BLAS

/-- `Array` provides all BLAS over the field `K`.

`K` might be complex number, in that case `R` is the corresponding real number. If `K` is just real
number then `R`

For examples for arrays of complex floats there is:
```
instance : BLAS ComplexFloatArray Float ComplexFloat := ...
```
for arrays of floats there is:
```
instance : BLAS FloatArray Float Float := ...
```
 -/
class BLAS (Array : Type*) (R K : outParam Type*)
  extends
    LevelOneData Array R K,
    LevelOneDataExt Array R K,
    LevelTwoData Array R K,
    LevelThreeData Array R K
  where

instance : BLAS Float64Array Float Float where


/-- BLAS with `Array` are lawful i.e. they satisfy expected linear algebra properties.

For floats this is not true, but sometimes we want to do source code transformations under the
assumption `LawfulBLAS FloatArray Float Float`. -/
class LawfulBLAS (Array : Type*) (R K : outParam Type*) [RCLike R] [RCLike K] [BLAS Array R K] : Prop
  extends
    LevelOneSpec Array R K

  where
