#!/usr/bin/env bash
# ---------------------------------------------------------------------------
# run_ci_local.sh – simulate the GitHub Actions CI pipeline locally.
# ---------------------------------------------------------------------------
# The script performs the same essential checks defined in
# .github/workflows/ci.yml but without any network interactions.
# It is handy when you want to verify the project passes BEFORE pushing.
#
# What it does:
# 1. Ensures NumPy is available (installs it into a venv under .venv if not).
# 2. Builds the Lean project (using Lake).
# 3. Executes the Lean × NumPy cross-check.
# ---------------------------------------------------------------------------

set -euo pipefail

PROJECT_ROOT=$(cd "$(dirname "$0")" && pwd)

# ---------------------------------------------------------------------------
# Python environment – create a lightweight venv under .venv if needed.
# ---------------------------------------------------------------------------

if ! command -v python3 >/dev/null 2>&1; then
  echo "❌ Python 3 is required but was not found in PATH." >&2
  exit 1
fi

# Attempt to use system Python with its packages first.
python3 - <<'PY'
import importlib, sys

try:
    importlib.import_module("numpy")
    sys.exit(0)
except ImportError:
    sys.exit(1)
PY

if [ $? -ne 0 ]; then
  # NumPy not available globally – fall back to venv and try to install.
  if [ ! -d "$PROJECT_ROOT/.venv" ]; then
    echo "🔹 Creating Python virtual environment (.venv)"
    python3 -m venv "$PROJECT_ROOT/.venv"
  fi

  source "$PROJECT_ROOT/.venv/bin/activate"

  python3 -m pip --quiet install --upgrade pip >/dev/null
  echo "🔹 Installing NumPy into .venv … (requires internet)"
  python3 -m pip install numpy || {
    echo "❌ Failed to install NumPy. Ensure internet access or pre-install it system-wide." >&2
    exit 1
  }
fi

# ---------------------------------------------------------------------------
# Build Lean project (will use cached .lake artefacts if present).
# ---------------------------------------------------------------------------

echo "🔹 Building Lean project with Lake …"
lake build >/dev/null

# ---------------------------------------------------------------------------
# Run cross-check.
# ---------------------------------------------------------------------------

echo "🔹 Running Lean × NumPy cross-check …"
python3 cross_check_numpy.py

echo "✅ Local CI succeeded!"
