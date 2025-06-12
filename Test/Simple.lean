import LeanBLAS.Spec.LevelOne

/-!
# Simple Test for LeanBLAS

A minimal test to verify the build system is working.
-/

namespace BLAS.Test.Simple

def test_basic : IO Unit := do
  IO.println "LeanBLAS Simple Test"
  IO.println "===================="
  IO.println "✓ Level One spec imported successfully"
  IO.println "✓ Basic IO operations working"
  IO.println "✓ Test framework operational"

end BLAS.Test.Simple

def main : IO Unit := do
  BLAS.Test.Simple.test_basic
  IO.println "\n✅ Simple test completed successfully!"
