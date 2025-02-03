# LeanBLAS

Bindings and specifications for BLAS (Basic Linear Algebra Subprograms).

The goal of the specification is to formalize mathematics of BLAS rather than what is happening on the bit level. Therefore we work with `Nat` rather than `Int32/64` and `ℝ` rather than `Float`.

## Build Instructions

### Prerequisites

Ensure you have the development files for C BLAS installed. On Ubuntu, you can install them with:

```bash
sudo apt-get install libblas-dev
```

### Building the Library

To build the main library, run:

```bash
lake build
```

### Running Tests

To execute the test suite, run:

```bash
lake test
```
