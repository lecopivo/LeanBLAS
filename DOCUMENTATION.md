# LeanBLAS Documentation Guide

## Enabling the Missing Documentation Linter

To enable the missing documentation linter in your Lean files, add this at the top of each file:

```lean
set_option linter.missingDocs true
```

This will ensure all public declarations have documentation.

## Documentation Standards

All public declarations should have documentation using Lean's docstring syntax:

```lean
/-- Brief description of what this declaration does. -/
```

For more complex declarations, use multi-line documentation:

```lean
/-- 
Brief description.

More detailed explanation with examples and usage notes.

## Example
```
example : usage
```
-/
```

## Module Documentation Status

- [x] lakefile.lean - Configuration file
- [ ] LeanBLAS/BLAS.lean - Main typeclass definitions (partial docs)
- [ ] LeanBLAS/Spec/Scalar.lean - Scalar type specifications
- [ ] LeanBLAS/Spec/LevelOne.lean - Level 1 BLAS operations
- [ ] LeanBLAS/Spec/LevelTwo.lean - Level 2 BLAS operations  
- [ ] LeanBLAS/Spec/LevelThree.lean - Level 3 BLAS operations
- [ ] LeanBLAS/CBLAS/*.lean - Implementation modules
- [ ] LeanBLAS/ComplexFloat.lean - Complex number support
- [ ] LeanBLAS/FFI/*.lean - Foreign function interface bindings