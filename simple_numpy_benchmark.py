#!/usr/bin/env python3
"""
Simple NumPy benchmark for Level 3 BLAS operations
Compares against theoretical BLAS performance
"""

import numpy as np
import time

def benchmark_gemm_sizes():
    """Benchmark GEMM for various matrix sizes"""
    print("Matrix Multiplication (GEMM) Performance Benchmark")
    print("=" * 70)
    print(f"{'Size':>10} {'Time (ms)':>12} {'GFLOPS':>10} {'% Peak':>10}")
    print("-" * 70)
    
    # Theoretical peak for a modern CPU (rough estimate)
    # Assume ~50 GFLOPS peak for double precision on a single core
    PEAK_GFLOPS = 50.0
    
    sizes = [10, 25, 50, 100, 150, 200, 300, 400, 500]
    
    for n in sizes:
        # Create random matrices
        A = np.random.randn(n, n).astype(np.float64)
        B = np.random.randn(n, n).astype(np.float64)
        
        # Determine iterations based on size
        if n <= 100:
            iterations = 1000
        elif n <= 300:
            iterations = 100
        else:
            iterations = 10
            
        # Warmup
        C = np.dot(A, B)
        
        # Benchmark
        start = time.perf_counter()
        for _ in range(iterations):
            C = np.dot(A, B)
        elapsed = time.perf_counter() - start
        
        # Calculate performance metrics
        time_ms = (elapsed / iterations) * 1000
        flops = 2.0 * n * n * n  # 2n³ operations for matrix multiplication
        gflops = (flops * iterations) / (elapsed * 1e9)
        percent_peak = (gflops / PEAK_GFLOPS) * 100
        
        print(f"{n:>10} {time_ms:>12.3f} {gflops:>10.3f} {percent_peak:>10.1f}%")

def benchmark_other_level3():
    """Benchmark other Level 3 operations"""
    print("\n\nOther Level 3 BLAS Operations")
    print("=" * 70)
    
    n = 100  # Fixed size for comparison
    iterations = 100
    
    # Test matrices
    A = np.random.randn(n, n).astype(np.float64)
    B = np.random.randn(n, n).astype(np.float64)
    C = np.random.randn(n, n).astype(np.float64)
    
    # Make A symmetric for SYMM test
    A_sym = (A + A.T) / 2
    
    # Make A upper triangular for TRMM test
    A_tri = np.triu(A)
    
    operations = [
        ("GEMM (General MM)", lambda: np.dot(A, B)),
        ("SYMM (Symmetric MM)", lambda: np.dot(A_sym, B)),
        ("SYRK (Symmetric Rank-k)", lambda: np.dot(A[:,:50], A[:,:50].T)),
        ("TRMM (Triangular MM)", lambda: np.dot(A_tri, B)),
    ]
    
    print(f"{'Operation':>25} {'Time (ms)':>12} {'GFLOPS':>10}")
    print("-" * 50)
    
    for name, op in operations:
        # Warmup
        _ = op()
        
        # Benchmark
        start = time.perf_counter()
        for _ in range(iterations):
            _ = op()
        elapsed = time.perf_counter() - start
        
        time_ms = (elapsed / iterations) * 1000
        # Approximate FLOP count (varies by operation)
        if "Rank-k" in name:
            flops = 2.0 * n * 50 * n  # n×k × k×n 
        else:
            flops = 2.0 * n * n * n
        gflops = (flops * iterations) / (elapsed * 1e9)
        
        print(f"{name:>25} {time_ms:>12.3f} {gflops:>10.3f}")

def main():
    """Run all benchmarks"""
    print("\nNumPy/BLAS Level 3 Performance Benchmark")
    print("Using NumPy version:", np.__version__)
    print("Matrix data type: float64 (double precision)")
    print("\n")
    
    benchmark_gemm_sizes()
    benchmark_other_level3()
    
    print("\n" + "=" * 70)
    print("Benchmark completed!")
    print("\nNote: These results show NumPy's performance, which typically")
    print("uses optimized BLAS libraries (OpenBLAS, MKL, etc.) underneath.")

if __name__ == "__main__":
    main()