# LeanBLAS

BLAS (Basic Linear Algebra Subprograms) bindings for Lean 4 with mathematical formalization and comprehensive testing.

## Overview

LeanBLAS provides type-safe BLAS operations with a focus on mathematical correctness. Unlike traditional BLAS libraries, LeanBLAS:

- Formalizes the mathematics of linear algebra operations
- Provides property-based testing that goes beyond typical numerical validation
- Includes formal mathematical specifications alongside efficient implementations
- Features the most comprehensive BLAS testing framework available

## Features

- **Complete BLAS Coverage**: Level 1, 2, and 3 operations with type-safe interfaces
- **FFI Bindings**: Efficient integration with OpenBLAS/system BLAS
- **Mathematical Formalization**: Specifications using Lean's type system
- **World-Class Testing**:
  - Property-based testing with automatic edge case discovery
  - Formal correctness proofs
  - Performance benchmarking with GFLOPS measurement
  - Numerical stability verification
- **Platform Support**: macOS and Linux (Windows not supported)

## Installation

### Prerequisites

**Ubuntu/Debian:**

```bash
sudo apt-get install libopenblas-dev
```

**macOS:**

```bash
brew install openblas
```

Windows is not supported.

### Build

```bash
git clone https://github.com/lecopivo/LeanBLAS
cd LeanBLAS
lake build
```

## Project Setup

### Using lakefile.lean

```lean
import Lake
open Lake DSL System

def linkArgs :=
  if System.Platform.isWindows then
    panic! "Windows is not supported!"
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib", "-L/usr/local/opt/openblas/lib", "-lblas"]
  else -- assuming Linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]

require leanblas from git "https://github.com/lecopivo/LeanBLAS" @ "main"
```

### Using lakefile.toml

```toml
[[require]]
name = "leanblas"
git = "https://github.com/lecopivo/LeanBLAS"
rev = "main"

[moreLinkArgs]
linux = ["-L/usr/lib/x86_64-linux-gnu/", "-lblas", "-lm"]
macos = ["-L/opt/homebrew/opt/openblas/lib", "-L/usr/local/opt/openblas/lib", "-lblas"]
```

## Quick Start

### Creating Arrays

LeanBLAS uses `Float64Array` for efficient numerical operations:

```lean
import LeanBLAS

-- Create arrays using the #f64[...] syntax
def x := #f64[1.0, 2.0, 3.0, 4.0]
def y := #f64[5.0, 6.0, 7.0, 8.0]
```

### Level 1 Examples (Vector Operations)

```lean
import LeanBLAS
import LeanBLAS.CBLAS.LevelOne

-- Dot product
def test_dot : IO Unit := do
  let x := #f64[1.0, 2.0, 3.0]
  let y := #f64[4.0, 5.0, 6.0]
  let result := BLAS.CBLAS.ddot 3 x 0 1 y 0 1
  IO.println s!"Dot product: {result}"  -- Expected: 32.0

-- Euclidean norm
def test_norm : IO Unit := do
  let x := #f64[3.0, 4.0]
  let norm := BLAS.CBLAS.dnrm2 2 x 0 1
  IO.println s!"Norm: {norm}"  -- Expected: 5.0

-- Scale vector
def test_scale : IO Unit := do
  let x := #f64[1.0, 2.0, 3.0]
  let scaled := BLAS.CBLAS.dscal 3 2.0 x 0 1
  IO.println s!"Scaled: {scaled.toFloatArray}"  -- Expected: [2.0, 4.0, 6.0]
```

### Level 2 Examples (Matrix-Vector Operations)

```lean
import LeanBLAS
import LeanBLAS.CBLAS.LevelTwo

-- Matrix-vector multiplication (GEMV)
def test_gemv : IO Unit := do
  -- A = [1 2; 3 4] (2x2 matrix in row-major order)
  let A := #f64[1.0, 2.0, 3.0, 4.0]
  let x := #f64[5.0, 6.0]
  let y := #f64[0.0, 0.0]
  
  -- y = 1.0 * A * x + 0.0 * y
  let result := BLAS.CBLAS.dgemv 
    BLAS.Order.RowMajor BLAS.Transpose.NoTrans
    2 2 1.0 A 0 2 x 0 1 0.0 y 0 1
  
  IO.println s!"Result: {result.toFloatArray}"  -- Expected: [17.0, 39.0]
```

### Level 3 Examples (Matrix-Matrix Operations)

```lean
import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

-- Matrix multiplication (GEMM)
def test_gemm : IO Unit := do
  -- A = [1 2; 3 4], B = [5 6; 7 8] (2x2 matrices)
  let A := #f64[1.0, 2.0, 3.0, 4.0]
  let B := #f64[5.0, 6.0, 7.0, 8.0]
  let C := #f64[0.0, 0.0, 0.0, 0.0]
  
  -- C = 1.0 * A * B + 0.0 * C
  let result := BLAS.CBLAS.dgemm 
    BLAS.Order.RowMajor 
    BLAS.Transpose.NoTrans BLAS.Transpose.NoTrans
    2 2 2 1.0 A 0 2 B 0 2 0.0 C 0 2
  
  IO.println s!"Result: {result.toFloatArray}"  -- Expected: [19.0, 22.0, 43.0, 50.0]
```

## Testing Framework

LeanBLAS features the most comprehensive BLAS testing suite available:

### Quick Test

```bash
lake exe SimpleTest       # Verify basic functionality
```

### Comprehensive Testing

```bash
lake exe ComprehensiveTests  # Run all tests with unified reporting
lake exe PropertyTests       # Property-based testing with random inputs
lake exe EdgeCaseTests       # Boundary conditions and numerical edge cases
lake exe CorrectnessTests    # Mathematical correctness verification
lake exe Level3Tests         # Level 3 BLAS operations testing
```

### Performance Analysis

```bash
lake exe BenchmarkTests      # Full performance analysis with scaling
lake exe BenchmarksFixedTest # Quick performance sanity check
lake exe Level3Benchmarks    # Matrix multiplication benchmarks
lake exe Gallery             # Showcase of all benchmarks
```

### Additional Testing Tools

- Python validation scripts: `test_level3.py`, `cross_check_numpy.py`
- Local CI script: `run_ci_local.sh`
- Level 3 test runner: `run_level3_tests.sh`

## Available Operations

### Level 1 (Vector-Vector)

- `dot`, `ddot`, `sdot` - Dot products
- `nrm2` - Euclidean norm
- `asum` - Sum of absolute values
- `axpy` - y := a*x + y
- `copy` - Copy vector
- `scal` - Scale vector
- `swap` - Swap vectors
- `rotg`, `rot` - Givens rotations

### Level 2 (Matrix-Vector)

- `gemv` - General matrix-vector multiplication
- `symv` - Symmetric matrix-vector multiplication
- `trmv` - Triangular matrix-vector multiplication
- `ger` - Rank-1 update
- `syr` - Symmetric rank-1 update
- `trsv` - Triangular solve

### Level 3 (Matrix-Matrix)

- `gemm` - General matrix-matrix multiplication
- `symm` - Symmetric matrix-matrix multiplication
- `trmm` - Triangular matrix-matrix multiplication
- `syrk` - Symmetric rank-k update
- `syr2k` - Symmetric rank-2k update
- `trsm` - Triangular solve with multiple right-hand sides

## Mathematical Formalization

LeanBLAS goes beyond traditional BLAS implementations by providing:

### Type-Safe Specifications

```lean
class LevelOneData (Array : Type*) (R K : Type*) where
  dot (N : Nat) (X : Array) (offX incX : Nat) (Y : Array) (offY incY : Nat) : K
  nrm2 (N : Nat) (X : Array) (offX incX : Nat) : R
  -- ... more operations
```

### Formal Properties

```lean
class LawfulBLAS (Array : Type*) (R K : Type*) [RCLike R] [RCLike K] [BLAS Array R K] : Prop
```

The `LawfulBLAS` class ensures operations satisfy mathematical laws like:

- Dot product commutativity: `dot(x,y) = dot(y,x)`
- Cauchy-Schwarz inequality: `|dot(x,y)| ≤ ||x|| * ||y||`
- Triangle inequality: `||x+y|| ≤ ||x|| + ||y||`

### API Design Philosophy

LeanBLAS uses offset and stride parameters for flexibility:

- `off`: Starting index in the array
- `inc`: Stride between elements (can be negative)

This allows working with:

- Subvectors without copying
- Non-contiguous data layouts
- Reverse iteration (negative stride)

## Project Structure

```text
LeanBLAS/
├── LeanBLAS/          # Main library code
│   ├── BLAS.lean      # Core typeclasses
│   ├── Spec/          # Mathematical specifications
│   ├── CBLAS/         # FFI implementations
│   └── FFI/           # Low-level bindings
├── Test/              # Comprehensive test suite
├── c/                 # C wrapper code
└── *.py               # Python validation scripts
```

## Documentation

- **In-Code Documentation**: Mathematical specifications in source files
- **`DOCUMENTATION.md`**: Documentation standards and guidelines
- **`STATUS.md`**: Detailed implementation status and test results
- **`AGENT.md`**: Development workflow and build commands

## Current Status

- ✅ Complete Level 1, 2, and 3 BLAS specifications
- ✅ FFI bindings to system BLAS
- ✅ Comprehensive testing framework
- ✅ Mathematical formalization
- ⚠️ Some proofs use `sorry` (work in progress)
- ⚠️ Complex number support partially implemented

## Contributing

LeanBLAS welcomes contributions! Key areas:

- Completing mathematical proofs
- Extending complex number support
- Adding more numerical stability tests
- Performance optimizations

## License

Apache 2.0
