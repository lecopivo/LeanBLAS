# LeanBLAS

Bindings and specifications for BLAS (Basic Linear Algebra Subprograms).

The goal of the specification is to formalize mathematics of BLAS rather than what is happening on the bit level. Therefore we work with `Nat` rather than `Int32/64` and `ℝ` rather than `Float`.

## Build Instructions

### Prerequisites

Ensure you have the development files for C BLAS installed.

On Ubuntu, you can install them with:

```bash
sudo apt-get install libopenblas-dev
```
On Mac, you can install them with:
```bash
brew install openblas
```

Currently we do not know of an easy way to build on Windows.

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

## Setting Up Your Project with LeanBLAS

To use `LeanBLAS` in your project, you need to:

- Add a `require` statement for `leanblas`.
- Set the `moreLinkArgs` option to include the location of your `libblas.so` (or dynamic library).

For example, a `lakefile.lean` for a project named `foo` might look like this:

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

package foo {
  moreLinkArgs := linkArgs
}

require leanblas from git "https://github.com/lecopivo/LeanBLAS" @ "v4.18.0"

@[default_target]
lean_lib Foo {
  roots := #[`Foo]
}
```
> **Note:** If your project depends on `mathlib`, make sure the `leanblas` version is compatible with it.

