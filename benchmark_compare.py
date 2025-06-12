#!/usr/bin/env python3
"""
benchmark_compare.py
====================
A simple benchmarking harness that measures the performance of NumPy's
vector dot-product on a few representative sizes and compares it to the
LeanBLAS benchmark suite (Test/Benchmarks.lean).

Usage
-----
Run from the project root after the Lean executables have been built::

    python benchmark_compare.py

The script prints two sections:
1. NumPy results (time/op, GFLOPS, ops/sec)
2. Raw output from `lake exe Benchmarks` (LeanBLAS side)

It does **not** attempt to parse the LeanBLAS output – human comparison is
typically sufficient and the exact formatting may evolve.  Feel free to extend
this script with a regex if automated dashboards are desired.
"""

from __future__ import annotations

import subprocess
import sys
import time
from pathlib import Path

try:
    import numpy as np  # type: ignore
except ImportError as exc:  # pragma: no cover – runtime dependency
    sys.stderr.write("NumPy is required for benchmarking but was not found.\n")
    raise

# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _select_iterations(size: int, base: int = 1_000) -> int:
    """Heuristic for choosing repeat count so total runtime is similar across sizes."""
    if size <= 0:
        return base
    return max(10, base // max(1, size // 100))


def _generate_vector(size: int) -> "np.ndarray":
    """Generate a test vector matching LeanBLAS' pattern (sinusoid)."""
    idx = np.arange(size, dtype=np.float64)
    return np.sin(idx * 0.1)


# ---------------------------------------------------------------------------
# NumPy micro-benchmarks (DOT, NORM, AXPY)
# ---------------------------------------------------------------------------


def _print_header(op_name: str) -> None:
    print(f"NumPy {op_name} benchmarks (double precision)")
    print("Size\tTime/op (s)\tGFLOPS\tops/sec")


def benchmark_numpy_dot(sizes: list[int]) -> None:
    _print_header("DOT-product")

    for size in sizes:
        x = _generate_vector(size)
        y = _generate_vector(size)

        iterations = _select_iterations(size)

        # Warm-up
        np.dot(x, y)

        start = time.perf_counter()
        for _ in range(iterations):
            np.dot(x, y)
        elapsed = time.perf_counter() - start

        time_per_op = elapsed / iterations
        flops = 2.0 * size  # mul + add per element
        gflops = flops / (time_per_op * 1e9)
        ops_per_sec = 1.0 / time_per_op

        print(f"{size}\t{time_per_op:.6e}\t{gflops:.3f}\t{ops_per_sec:,.0f}")


def benchmark_numpy_norm(sizes: list[int]) -> None:
    _print_header("NORM (L2)")

    for size in sizes:
        x = _generate_vector(size)

        iterations = _select_iterations(size)

        np.linalg.norm(x)

        start = time.perf_counter()
        for _ in range(iterations):
            np.linalg.norm(x)
        elapsed = time.perf_counter() - start

        time_per_op = elapsed / iterations
        flops = 2.0 * size + 1  # mul + add + sqrt
        gflops = flops / (time_per_op * 1e9)
        ops_per_sec = 1.0 / time_per_op

        print(f"{size}\t{time_per_op:.6e}\t{gflops:.3f}\t{ops_per_sec:,.0f}")


def benchmark_numpy_axpy(sizes: list[int]) -> None:
    _print_header("AXPY (y = a*x + y)")

    alpha = 2.5
    for size in sizes:
        x = _generate_vector(size)
        y = _generate_vector(size)

        iterations = _select_iterations(size)

        y + alpha * x  # warm-up

        start = time.perf_counter()
        for _ in range(iterations):
            y = alpha * x + y  # AXPY equivalent
        elapsed = time.perf_counter() - start

        time_per_op = elapsed / iterations
        flops = 2.0 * size  # mul + add
        gflops = flops / (time_per_op * 1e9)
        ops_per_sec = 1.0 / time_per_op

        print(f"{size}\t{time_per_op:.6e}\t{gflops:.3f}\t{ops_per_sec:,.0f}")


# ---------------------------------------------------------------------------
# LeanBLAS benchmark invocation
# ---------------------------------------------------------------------------


def run_lean_bench() -> None:
    """Invoke `lake exe Benchmarks` and stream its stdout."""
    # Ensure we are in the repo root where lakefile lives.
    repo_root = Path(__file__).resolve().parent
    try:
        result = subprocess.run(
            ["lake", "exe", "BenchmarksFixedTest"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        )
    except FileNotFoundError:
        sys.stderr.write(
            "Error: `lake` command not found. Ensure Lean's Lake is installed and on PATH.\n"
        )
        return
    except subprocess.CalledProcessError as exc:
        sys.stderr.write("`lake exe BenchmarkTests` failed – see output below.\n")
        sys.stderr.write(exc.stdout)
        sys.stderr.write(exc.stderr)
        return

    print("\nLeanBLAS benchmark output (raw):\n" + "-" * 40)
    print(result.stdout)

    # ------------------------------------------------------------------
    # Simple correctness cross-check versus NumPy for the 1M-element test
    # ------------------------------------------------------------------

    import re, numpy as np  # noqa: E402  (import only if Lean run succeeded)

    # Helper to generate the same test vector (1, 2, 3, …) used in Lean.
    def _gen(size: int) -> "np.ndarray":
        return np.arange(1, size + 1, dtype=np.float64)

    dot_match = re.search(r"Checksum \(acc\):\s+([0-9.eE+\-]+)\s*\n", result.stdout)
    norm_match = re.search(r"NORM .*?Checksum \(acc\):\s+([0-9.eE+\-]+)\s*\n", result.stdout, re.S)
    axpy_match = re.search(r"AXPY .*?Checksum:\s+([0-9.eE+\-]+)\s*\n", result.stdout, re.S)
    mem_match = re.search(r"Memory Bandwidth .*?Checksum:\s+([0-9.eE+\-]+)\s*\n", result.stdout, re.S)

    size = 1_000_000
    iterations = 10
    vec = _gen(size)

    # ---------- DOT checksum ----------
    if dot_match:
        lean_checksum = float(dot_match.group(1))

        py_checksum = 0.0
        for i in range(iterations):
            py_checksum += float(np.dot(vec[i:], vec[i:]))

        print("Dot product checksum comparison (sum over 10 sliced dots):")
        print(f"  Lean: {lean_checksum:.6e}\n  NumPy: {py_checksum:.6e}\n  diff: {abs(lean_checksum-py_checksum):.3e}")
    else:
        print("Could not parse dot-product checksum from Lean output.")

    # ---------- Norm checksum ----------
    if norm_match:
        lean_checksum = float(norm_match.group(1))

        py_checksum = 0.0
        for i in range(iterations):
            py_checksum += float(np.linalg.norm(vec[i:]))

        print("\nNorm checksum comparison:")
        print(f"  Lean: {lean_checksum:.6e}\n  NumPy: {py_checksum:.6e}\n  diff: {abs(lean_checksum-py_checksum):.3e}")
    else:
        print("Could not parse norm checksum from Lean output.")

    # ---------- AXPY checksum ----------
    if axpy_match:
        lean_checksum = float(axpy_match.group(1))

        alpha = 2.5
        x = vec.copy()
        y = vec.copy()
        py_checksum = 0.0
        for i in range(iterations):
            n_i = size - i
            y[i : i + n_i] = alpha * x[i : i + n_i] + y[i : i + n_i]
            py_checksum += float(y[i])

        print("\nAXPY checksum comparison:")
        print(f"  Lean: {lean_checksum:.6e}\n  NumPy: {py_checksum:.6e}\n  diff: {abs(lean_checksum-py_checksum):.3e}")
    else:
        print("Could not parse AXPY checksum from Lean output.")

    # ---------- DSUM checksum ----------
    if mem_match:
        lean_checksum = float(mem_match.group(1))

        sum_val = float(np.sum(vec))
        py_checksum = iterations * sum_val

        print("\nDSUM checksum comparison:")
        print(f"  Lean: {lean_checksum:.6e}\n  NumPy: {py_checksum:.6e}\n  diff: {abs(lean_checksum-py_checksum):.3e}")
    else:
        print("Could not parse DSUM checksum from Lean output.")


# ---------------------------------------------------------------------------
# Entry-point
# ---------------------------------------------------------------------------


def main() -> None:
    print("=== LeanBLAS vs NumPy Benchmarks ===")
    print()

    sizes = [100, 1_000, 10_000, 100_000]

    # --- NumPy section ---
    benchmark_numpy_dot(sizes)
    print()
    benchmark_numpy_norm(sizes)
    print()
    benchmark_numpy_axpy(sizes)

    # --- LeanBLAS section ---
    print()
    run_lean_bench()


if __name__ == "__main__":
    main()
