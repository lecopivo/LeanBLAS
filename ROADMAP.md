# LeanBLAS Development Roadmap

## Current State (January 2025)

### ✅ Completed
- **Level 1-3 BLAS for Float64**: Full implementation with FFI bindings
- **Comprehensive test suite**: Property-based, edge case, and correctness tests
- **Documentation**: Module-level docs for all major components
- **Bug fixes**: Resolved cblas_daxpby linking issue
- **PR #4**: Level 3 BLAS implementation ready for merge

### 🔍 Key Insights from Development
1. **FFI is well-designed**: ByteArray wrappers provide zero-copy C compatibility
2. **Specification-first approach**: Clean separation between math specs and implementations
3. **Testing infrastructure**: Robust framework already in place
4. **Non-standard functions**: Some extended BLAS functions need manual implementation

## Strategic Priorities

### Phase 1: Complex Number Support (Q1 2025)
**Rationale**: Natural extension of existing functionality, high user value

#### 1.1 ComplexFloat64 Level 1 (High Priority)
- Implement `zdot`, `zdotc`, `zdotu` (complex dot products)
- Add `dznrm2`, `dzasum` (mixed precision norms)
- Implement `zscal`, `zaxpy`, `zcopy`, `zswap`
- **Technical approach**: 
  - Extend existing FFI patterns
  - Use ComplexFloat64Array (already defined)
  - Add complex-specific specifications

#### 1.2 ComplexFloat64 Level 2 (High Priority)
- Implement `zgemv`, `zsymv`, `zhemv` (matrix-vector)
- Add `zger`, `zgeru`, `zgerc` (rank-1 updates)
- Implement `ztrsv`, `ztrmv` (triangular operations)
- **Challenges**: Conjugate transpose handling

#### 1.3 ComplexFloat64 Level 3 (High Priority)
- Implement `zgemm` (complex matrix multiplication)
- Add `zsymm`, `zhemm`, `zsyrk`, `zherk`
- **Performance critical**: Ensure efficient complex arithmetic

### Phase 2: Formal Verification (Q2 2025)
**Rationale**: Unique value proposition for LeanBLAS

#### 2.1 Level 1 Proofs (Medium Priority)
- **Dot product properties**: Commutativity for real, conjugate symmetry for complex
- **Norm properties**: Triangle inequality, scaling properties
- **Vector operation properties**: Linearity of axpy, swap involution
- **Approach**: Build on existing specifications, use Mathlib tactics

#### 2.2 Matrix Operation Proofs (Medium Priority)
- **Associativity**: Prove (AB)C = A(BC) for compatible dimensions
- **Distributivity**: Prove A(B+C) = AB + AC
- **Identity properties**: AI = IA = A
- **Challenges**: Floating-point approximation handling

#### 2.3 Numerical Stability Bounds (Medium Priority)
- Establish error bounds for operations
- Prove backward stability where applicable
- **Research component**: May require new techniques

### Phase 3: Performance Analysis (Q2 2025)
**Rationale**: Understand and minimize Lean overhead

#### 3.1 Benchmarking Suite (Medium Priority)
- Compare Lean BLAS vs direct C calls
- Measure FFI overhead
- Profile memory allocation patterns
- **Deliverable**: Performance dashboard

#### 3.2 Optimization Opportunities
- Identify bottlenecks in Lean layer
- Optimize array conversions
- Consider specialized implementations for small matrices

### Phase 4: Extended Functionality (Q3 2025)
**Rationale**: Expand beyond dense linear algebra

#### 4.1 Sparse Matrix Support (Low Priority)
- Implement CSR (Compressed Sparse Row) format
- Add CSC (Compressed Sparse Column) format
- Basic SpMV (sparse matrix-vector) operations
- **Design decision**: New module or extend existing?

#### 4.2 Banded Matrix Specializations (Low Priority)
- Optimize operations for banded matrices
- Add specialized storage formats
- **Use cases**: Finite difference methods, spline interpolation

### Phase 5: Hardware Acceleration (Q4 2025)
**Rationale**: Future-proofing for heterogeneous computing

#### 5.1 GPU Architecture Design (Low Priority)
- Evaluate CUDA vs OpenCL vs Vulkan Compute
- Design async operation interface
- Memory management strategy
- **Major undertaking**: Possibly separate project

#### 5.2 SIMD Optimizations
- Explore Lean's SIMD support
- Implement vectorized operations for small sizes
- **Platform-specific**: Need careful abstraction

## Implementation Guidelines

### Code Quality Standards
1. **Every new function needs**:
   - Mathematical specification in Spec module
   - FFI binding with documentation
   - CBLAS implementation instance
   - Unit tests and property tests

2. **Documentation requirements**:
   - Module-level overview
   - Function-level specifications
   - Performance characteristics
   - Usage examples

3. **Testing approach**:
   - Property-based tests for mathematical properties
   - Edge case coverage (zero, identity, etc.)
   - Cross-validation with NumPy/reference implementations
   - Performance regression tests

### Development Workflow
1. **Feature branches**: One feature per branch
2. **PR process**: Include tests, docs, and benchmarks
3. **Review criteria**: Correctness, performance, documentation
4. **Integration testing**: Full test suite before merge

## Success Metrics
- **Adoption**: GitHub stars, dependent projects
- **Performance**: Within 10% of native BLAS for large matrices
- **Correctness**: 100% test coverage, formal proofs for core operations
- **Documentation**: Every public API fully documented
- **Community**: Active contributors, responsive issue resolution

## Open Questions
1. Should complex number support be a separate package?
2. How to handle mixed-precision operations?
3. What level of formal verification is practical?
4. Should we support arbitrary precision arithmetic?
5. How to integrate with Lean's mathematical libraries?

## Next Immediate Steps
1. Get PR #4 merged
2. Set up complex number FFI infrastructure
3. Implement zdot as proof of concept
4. Design formal verification framework
5. Create performance benchmarking harness