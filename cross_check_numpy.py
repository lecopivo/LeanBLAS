#!/usr/bin/env python3
"""LeanBLAS × NumPy automated cross-check.

Runs the *quick* Lean benchmark executable (`lake exe BenchmarksFixedTest`),
extracts the checksum totals for DOT, NORM, AXPY and DSUM, recomputes the same
loops with NumPy and fails (non-zero exit code) if they differ beyond a tiny
tolerance (1e-8 *|value|).

Intended to be used in CI: just invoke this script from the repository root.
"""

from __future__ import annotations

import math
import re
import subprocess
import sys
from pathlib import Path
from typing import Final


try:
    import numpy as np  # type: ignore
except ImportError:
    sys.stderr.write("NumPy is required for cross-checking but was not found.\n")
    sys.exit(1)


RE_DOT: Final = re.compile(r"Checksum \(acc\):\s+([0-9.eE+\-]+)")
RE_NORM: Final = re.compile(r"NORM.*?Checksum \(acc\):\s+([0-9.eE+\-]+)", re.S)
RE_AXPY: Final = re.compile(r"AXPY.*?Checksum:\s+([0-9.eE+\-]+)", re.S)
RE_DSUM: Final = re.compile(r"Memory Bandwidth.*?Checksum:\s+([0-9.eE+\-]+)", re.S)

SIZE_DOT_NORM_AXPY: Final = 1_000_000
SIZE_DSUM: Final = 10_000_000
ITERATIONS: Final = 10  # hard-coded in BenchmarksFixed

TOL_REL: Final = 1e-8  # relative tolerance


def run_lean() -> str:
    """Execute the Lean quick benchmark and return its stdout."""

    try:
        res = subprocess.run(
            ["lake", "exe", "BenchmarksFixedTest"],
            capture_output=True,
            text=True,
            check=True,
        )
    except subprocess.CalledProcessError as exc:
        sys.stderr.write("Lean benchmark failed – output:\n" + exc.stdout)
        sys.stderr.write(exc.stderr)
        sys.exit(exc.returncode)

    return res.stdout


def gen_vec(size: int) -> "np.ndarray":
    """Generate the same vector pattern used in BenchmarksFixed (1,2,3,…)."""

    return np.arange(1, size + 1, dtype=np.float64)


def close_enough(a: float, b: float) -> bool:
    return math.isclose(a, b, rel_tol=TOL_REL, abs_tol=0.0)


def check_dot(lean_val: float) -> None:
    x = gen_vec(SIZE_DOT_NORM_AXPY)
    suma = 0.0
    for i in range(ITERATIONS):
        v = x[i:]
        suma += float(np.dot(v, v))

    if not close_enough(suma, lean_val):
        raise AssertionError(
            f"DOT checksum mismatch – Lean {lean_val:.12e} vs NumPy {suma:.12e}"
        )


def check_norm(lean_val: float) -> None:
    x = gen_vec(SIZE_DOT_NORM_AXPY)
    suma = 0.0
    for i in range(ITERATIONS):
        suma += float(np.linalg.norm(x[i:]))

    if not close_enough(suma, lean_val):
        raise AssertionError(
            f"NORM checksum mismatch – Lean {lean_val:.12e} vs NumPy {suma:.12e}"
        )


def check_axpy(lean_val: float) -> None:
    size = SIZE_DOT_NORM_AXPY
    alpha = 2.5
    x = gen_vec(size)
    y = gen_vec(size)
    checksum = 0.0
    for i in range(ITERATIONS):
        n_i = size - i
        # Slice-update in place like Lean loop
        y[i : i + n_i] = alpha * x[i : i + n_i] + y[i : i + n_i]
        checksum += float(y[i])

    if not close_enough(checksum, lean_val):
        raise AssertionError(
            f"AXPY checksum mismatch – Lean {lean_val:.12e} vs NumPy {checksum:.12e}"
        )


def check_dsum(lean_val: float) -> None:
    x = gen_vec(SIZE_DSUM)
    single = float(np.sum(x))
    total = ITERATIONS * single
    if not close_enough(total, lean_val):
        raise AssertionError(
            f"DSUM checksum mismatch – Lean {lean_val:.12e} vs NumPy {total:.12e}"
        )


def main() -> None:
    out = run_lean()

    dot_m = RE_DOT.search(out)
    norm_m = RE_NORM.search(out)
    axpy_m = RE_AXPY.search(out)
    dsum_m = RE_DSUM.search(out)

    if not (dot_m and norm_m and axpy_m and dsum_m):
        sys.stderr.write("Failed to parse one or more checksum lines from Lean output.\n")
        sys.exit(2)

    try:
        check_dot(float(dot_m.group(1)))
        check_norm(float(norm_m.group(1)))
        check_axpy(float(axpy_m.group(1)))
        check_dsum(float(dsum_m.group(1)))
    except AssertionError as exc:
        sys.stderr.write(str(exc) + "\n")
        sys.exit(3)

    print("All Lean checksums match NumPy ✓")


if __name__ == "__main__":
    main()
