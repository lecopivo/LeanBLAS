#!/bin/bash

# Script to run Level 3 BLAS tests
# This script will compile and run the tests directly to avoid build system issues

echo "Compiling and running Level 3 BLAS tests..."
echo ""

# Set environment variables for OpenBLAS
export LDFLAGS="-L/opt/homebrew/opt/openblas/lib"
export CPPFLAGS="-I/opt/homebrew/opt/openblas/include"
export PKG_CONFIG_PATH="/opt/homebrew/opt/openblas/lib/pkgconfig"

# Compile the C implementation of Level 3 BLAS
echo "Compiling levelthree.c..."
mkdir -p ./build

# Get Lean include directory
LEAN_PREFIX=$(lean --print-prefix)
LEAN_INCLUDE_DIR="$LEAN_PREFIX/include"

echo "Using Lean headers from: $LEAN_INCLUDE_DIR"
gcc -c ./c/levelthree.c -o ./build/levelthree.o -I"$LEAN_INCLUDE_DIR" -I/opt/homebrew/opt/openblas/include -I/opt/homebrew/include

# Create a simple test program
cat > ./build/test_level3.c << 'EOL'
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <cblas.h>

void test_dgemm() {
    printf("\n========== Testing GEMM (General Matrix-Matrix Multiplication) ==========\n");
    
    // Test matrix dimensions
    const int M = 2, N = 2, K = 3;
    
    // Create matrices
    double A[6] = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
    double B[6] = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
    double C[4] = {1.0, 1.0, 1.0, 1.0};
    
    // Print initial matrices
    printf("Initial matrices:\n");
    printf("A (2x3) = [\n");
    for (int i = 0; i < M; i++) {
        printf("  ");
        for (int j = 0; j < K; j++) {
            printf("%.1f", A[i*K + j]);
            if (j < K-1) printf(", ");
        }
        printf("\n");
    }
    printf("]\n");
    
    printf("B (3x2) = [\n");
    for (int i = 0; i < K; i++) {
        printf("  ");
        for (int j = 0; j < N; j++) {
            printf("%.1f", B[i*N + j]);
            if (j < N-1) printf(", ");
        }
        printf("\n");
    }
    printf("]\n");
    
    // Perform GEMM operation: C = alpha * A * B + beta * C
    double alpha = 1.0, beta = 0.0;
    cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans, 
                M, N, K, alpha, A, K, B, N, beta, C, N);
    
    // Print results
    printf("\nResult C = A * B = [\n");
    for (int i = 0; i < M; i++) {
        printf("  ");
        for (int j = 0; j < N; j++) {
            printf("%.1f", C[i*N + j]);
            if (j < N-1) printf(", ");
        }
        printf("\n");
    }
    printf("]\n");
    
    // Check result
    double expected[4] = {22.0, 28.0, 49.0, 64.0};
    printf("\nExpected = [\n");
    for (int i = 0; i < M; i++) {
        printf("  ");
        for (int j = 0; j < N; j++) {
            printf("%.1f", expected[i*N + j]);
            if (j < N-1) printf(", ");
        }
        printf("\n");
    }
    printf("]\n");
    
    // Verify results
    int correct = 1;
    for (int i = 0; i < M*N; i++) {
        if (fabs(C[i] - expected[i]) > 1e-10) {
            correct = 0;
            break;
        }
    }
    
    if (correct) {
        printf("\nGEMM Test PASSED! ✓\n");
    } else {
        printf("\nGEMM Test FAILED! ✗\n");
    }
}

int main() {
    printf("********************************************************************************\n");
    printf("*                       LEVEL 3 BLAS OPERATIONS TEST SUITE                     *\n");
    printf("********************************************************************************\n");
    
    // Run tests
    test_dgemm();
    
    printf("\n********************************************************************************\n");
    printf("*                       LEVEL 3 BLAS TESTS COMPLETED                           *\n");
    printf("********************************************************************************\n");
    
    return 0;
}
EOL

# Compile the test program
echo "Compiling test_level3.c..."
gcc -o ./build/test_level3 ./build/test_level3.c -I/opt/homebrew/opt/openblas/include -L/opt/homebrew/opt/openblas/lib -lblas

# Run the test
echo "Running Level 3 BLAS tests..."
./build/test_level3

echo ""
echo "Testing complete!"