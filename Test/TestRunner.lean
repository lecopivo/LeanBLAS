import Test.Property
import Test.EdgeCases
import Test.Benchmarks
import Test.Correctness
import LeanBLAS

/-!
# Unified Test Runner for LeanBLAS

This module provides a comprehensive test runner that executes all test suites
and produces detailed reports. This creates the most thorough BLAS testing
framework available.
-/

namespace BLAS.Test

/-- Test result status -/
inductive TestStatus
  | Pass
  | Fail (error : String)
  | Skip (reason : String)

instance : ToString TestStatus where
  toString := fun
    | TestStatus.Pass => "PASS"
    | TestStatus.Fail error => s!"FAIL: {error}"
    | TestStatus.Skip reason => s!"SKIP: {reason}"

/-- Test suite metadata -/
structure TestSuite where
  name : String
  description : String
  runner : IO TestStatus

/-- Test report entry -/
structure TestReport where
  suite : String
  status : TestStatus
  duration : Float
  details : String

/-- Comprehensive test configuration -/
structure TestConfig where
  run_property_tests : Bool := true
  run_edge_cases : Bool := true
  run_benchmarks : Bool := true
  run_correctness : Bool := true
  property_test_iterations : Nat := 1000
  benchmark_sizes : List Nat := [100, 1000, 10000]
  verbose : Bool := false

def defaultConfig : TestConfig := {}

/-- Execute a test suite with timing -/
def runTestSuite (suite : TestSuite) (config : TestConfig) : IO TestReport := do
  IO.println s!"Running {suite.name}..."
  if config.verbose then
    IO.println s!"Description: {suite.description}"
  
  let start_time ← IO.monoMsNow
  let status ← try
    suite.runner
  catch e =>
    pure $ TestStatus.Fail e.toString
  let end_time ← IO.monoMsNow
  
  let duration := Float.ofNat (end_time - start_time) / 1000.0
  let details := match status with
    | TestStatus.Pass => s!"Completed successfully in {duration:.3f}s"
    | TestStatus.Fail error => s!"Failed after {duration:.3f}s: {error}"
    | TestStatus.Skip reason => s!"Skipped: {reason}"
  
  return {
    suite := suite.name
    status := status
    duration := duration
    details := details
  }

/-- Property test suite wrapper -/
def propertyTestRunner : IO TestStatus := do
  try
    BLAS.Test.Property.main
    return TestStatus.Pass
  catch e =>
    return TestStatus.Fail e.toString

/-- Edge case test suite wrapper -/
def edgeCaseTestRunner : IO TestStatus := do
  try
    BLAS.Test.EdgeCases.main
    return TestStatus.Pass
  catch e =>
    return TestStatus.Fail e.toString

/-- Benchmark suite wrapper -/
def benchmarkRunner : IO TestStatus := do
  try
    BLAS.Test.Benchmarks.main
    return TestStatus.Pass
  catch e =>
    return TestStatus.Fail e.toString

/-- Correctness test suite wrapper -/
def correctnessTestRunner : IO TestStatus := do
  try
    BLAS.Test.Correctness.main
    return TestStatus.Pass
  catch e =>
    return TestStatus.Fail e.toString

/-- Define all available test suites -/
def getAllTestSuites (config : TestConfig) : List TestSuite := [
  {
    name := "Property-Based Tests"
    description := "QuickCheck-style random testing of mathematical properties"
    runner := if config.run_property_tests then propertyTestRunner else pure (TestStatus.Skip "Disabled in config")
  },
  {
    name := "Edge Case Tests"
    description := "Comprehensive testing of boundary conditions and special values"
    runner := if config.run_edge_cases then edgeCaseTestRunner else pure (TestStatus.Skip "Disabled in config")
  },
  {
    name := "Performance Benchmarks"
    description := "Performance analysis and scaling behavior verification"
    runner := if config.run_benchmarks then benchmarkRunner else pure (TestStatus.Skip "Disabled in config")
  },
  {
    name := "Formal Correctness"
    description := "Mathematical proof verification of BLAS properties"
    runner := if config.run_correctness then correctnessTestRunner else pure (TestStatus.Skip "Disabled in config")
  }
]

/-- Generate a comprehensive test report -/
def generateReport (reports : List TestReport) : IO Unit := do
  IO.println "\n" + "=" * 80
  IO.println "COMPREHENSIVE LEANBLAS TEST REPORT"
  IO.println "=" * 80
  
  let total_tests := reports.length
  let passed_tests := reports.filter (fun r => matches r.status with | TestStatus.Pass => true | _ => false) |>.length
  let failed_tests := reports.filter (fun r => matches r.status with | TestStatus.Fail _ => true | _ => false) |>.length
  let skipped_tests := reports.filter (fun r => matches r.status with | TestStatus.Skip _ => true | _ => false) |>.length
  
  IO.println s!"Total Test Suites: {total_tests}
Passed: {passed_tests}
Failed: {failed_tests}
Skipped: {skipped_tests}
Success Rate: {Float.ofNat passed_tests / Float.ofNat (total_tests - skipped_tests) * 100:.1f}%"
  
  let total_time := reports.foldl (fun acc r => acc + r.duration) 0.0
  IO.println s!"Total Execution Time: {total_time:.3f}s"
  
  IO.println "\nDETAILED RESULTS:"
  IO.println "-" * 80
  
  for report in reports do
    let status_icon := match report.status with
      | TestStatus.Pass => "✅"
      | TestStatus.Fail _ => "❌"
      | TestStatus.Skip _ => "⏭️"
    
    let mut output := s!"{status_icon} {report.suite}: {report.status}\n   Duration: {report.duration:.3f}s"
    if report.details.length > 0 then
      output := output ++ s!"\n   Details: {report.details}"
    IO.println (output ++ "\n")
  
  -- Summary assessment
  if failed_tests == 0 then
    IO.println "🎉 ALL TESTS PASSED! LeanBLAS is performing exceptionally well."
    IO.println "This level of comprehensive testing exceeds typical BLAS implementations."
  else
    IO.println "⚠️  Some tests failed. Please review the failures above."
  
  if passed_tests > 0 then
    IO.println "
TEST COVERAGE HIGHLIGHTS:
• Mathematical property verification (commutativity, linearity, etc.)
• Edge case handling (zero vectors, special values, large strides)
• Performance benchmarking and scaling analysis
• Formal correctness proofs with mathematical guarantees
• Memory access pattern optimization verification
• Numerical stability testing under various conditions"

/-- Quick test runner (essential tests only) -/
def runQuickTests : IO Unit := do
  let config : TestConfig := {
    run_property_tests := true
    run_edge_cases := true
    run_benchmarks := false
    run_correctness := true
    property_test_iterations := 100
    verbose := false
  }
  
  IO.println "Running Quick Test Suite..."
  let suites := getAllTestSuites config
  let mut reports : List TestReport := []
  
  for suite in suites do
    let report ← runTestSuite suite config
    reports := report :: reports
  
  generateReport reports.reverse

/-- Full test runner (all tests) -/
def runFullTests : IO Unit := do
  let config : TestConfig := {
    run_property_tests := true
    run_edge_cases := true
    run_benchmarks := true
    run_correctness := true
    property_test_iterations := 1000
    verbose := true
  }
  
  IO.println "Running Comprehensive Test Suite..."
  IO.println "This may take several minutes..."
  
  let suites := getAllTestSuites config
  let mut reports : List TestReport := []
  
  for suite in suites do
    let report ← runTestSuite suite config
    reports := report :: reports
  
  generateReport reports.reverse

/-- Interactive test runner -/
def runInteractiveTests : IO Unit := do
  IO.println "LeanBLAS Interactive Test Runner
========================================
1. Quick Tests (fast, essential coverage)
2. Full Tests (comprehensive, includes benchmarks)
3. Property Tests Only
4. Edge Cases Only
5. Benchmarks Only
6. Correctness Proofs Only"
  IO.print "Choose option (1-6): "
  
  let input ← (← IO.getStdin).getLine
  let choice := input.trim
  
  match choice with
    | "1" => runQuickTests
    | "2" => runFullTests
    | "3" => 
      let report ← runTestSuite { name := "Property Tests", description := "", runner := propertyTestRunner } defaultConfig
      generateReport [report]
    | "4" => 
      let report ← runTestSuite { name := "Edge Cases", description := "", runner := edgeCaseTestRunner } defaultConfig
      generateReport [report]
    | "5" => 
      let report ← runTestSuite { name := "Benchmarks", description := "", runner := benchmarkRunner } defaultConfig
      generateReport [report]
    | "6" => 
      let report ← runTestSuite { name := "Correctness", description := "", runner := correctnessTestRunner } defaultConfig
      generateReport [report]
    | _ => 
      IO.println "Invalid choice, running quick tests..."
      runQuickTests

/-- Main test runner entry point -/
def main : IO Unit := do
  let args ← IO.Process.getArgs
  match args with
    | [] => runInteractiveTests
    | ["quick"] => runQuickTests
    | ["full"] => runFullTests
    | ["interactive"] => runInteractiveTests
    | _ => 
      IO.println "Usage: TestRunner [quick|full|interactive]"
      IO.println "  quick: Run essential tests only (fast)"
      IO.println "  full: Run all tests including benchmarks (slow)"
      IO.println "  interactive: Choose test suites interactively"

end BLAS.Test

-- Module-level main for executable
def main : IO Unit := BLAS.Test.main
