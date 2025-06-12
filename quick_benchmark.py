#!/usr/bin/env python3
"""
Quick benchmark to test LeanBLAS Level 3 operations vs NumPy
Designed to complete in under 2 minutes
"""

import numpy as np
import time
import subprocess
import sys

def benchmark_numpy_gemm():
    """Benchmark NumPy matrix multiplication with various sizes"""
    print("=== NumPy GEMM (Matrix Multiplication) Benchmarks ===")
    print("Size\tTime (ms)\tGFLOPS")
    
    # Test small sizes that should complete quickly
    sizes = [10, 50, 100, 200]
    
    for size in sizes:
        # Create random matrices
        A = np.random.randn(size, size).astype(np.float64)
        B = np.random.randn(size, size).astype(np.float64)
        C = np.zeros((size, size), dtype=np.float64)
        
        # Warmup
        _ = A @ B
        
        # Time the operation
        iterations = max(10, 1000 // size)  # More iterations for smaller sizes
        start = time.perf_counter()
        for _ in range(iterations):
            C = A @ B
        elapsed = time.perf_counter() - start
        
        # Calculate metrics
        time_per_op = elapsed / iterations * 1000  # Convert to milliseconds
        flops = 2.0 * size * size * size  # 2n³ for matrix multiplication
        gflops = (flops * iterations) / (elapsed * 1e9)
        
        print(f"{size}x{size}\t{time_per_op:.3f}\t{gflops:.3f}")

def test_lean_gemm():
    """Create and run a simple Lean test for GEMM"""
    print("\n=== Testing LeanBLAS GEMM ===")
    
    # Create a minimal test file
    test_content = """
import LeanBLAS
import LeanBLAS.CBLAS.LevelThree

def main : IO Unit := do
  -- Create small 2x2 matrices for quick test
  let A := #f64[1.0, 2.0, 3.0, 4.0]
  let B := #f64[5.0, 6.0, 7.0, 8.0]
  let C := #f64[0.0, 0.0, 0.0, 0.0]
  
  -- Perform matrix multiplication
  let result := BLAS.CBLAS.gemm 
    BLAS.Order.RowMajor 
    BLAS.Transpose.NoTrans 
    BLAS.Transpose.NoTrans
    2 2 2  -- M, N, K dimensions
    1.0    -- alpha
    A 0 2  -- A matrix
    B 0 2  -- B matrix  
    0.0    -- beta
    C 0 2  -- C matrix
    
  IO.println "Test completed. Result computed successfully."
  IO.println s!"First element: {(result.toFloatArray.get 0)}"
"""
    
    # Write test file
    with open("minimal_gemm_test.lean", "w") as f:
        f.write(test_content)
    
    # Try to run it
    try:
        print("Running minimal GEMM test...")
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "minimal_gemm_test.lean"],
            capture_output=True,
            text=True,
            timeout=30  # 30 second timeout for safety
        )
        
        if result.returncode == 0:
            print("✓ LeanBLAS GEMM test passed!")
            print(result.stdout)
        else:
            print("✗ LeanBLAS GEMM test failed!")
            print("Error:", result.stderr)
            
    except subprocess.TimeoutExpired:
        print("✗ Test timed out after 30 seconds")
    except Exception as e:
        print(f"✗ Error running test: {e}")

def main():
    """Run quick benchmarks"""
    print("Quick Benchmark Test - Should complete in < 1 minute")
    print("=" * 60)
    
    # First run the NumPy benchmarks
    benchmark_numpy_gemm()
    
    # Then test LeanBLAS
    test_lean_gemm()
    
    print("\n" + "=" * 60)
    print("Quick benchmark completed!")

if __name__ == "__main__":
    main()