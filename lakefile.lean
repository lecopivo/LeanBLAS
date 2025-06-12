import Lake

open Lake DSL System Lean Elab

def linkArgs := -- (#[] : Array String)
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-L/opt/homebrew/opt/openblas/lib", "-lblas"]
  else -- assuming linux
    #["-L/usr/lib/x86_64-linux-gnu/", "-lblas"]
def inclArgs :=
  if System.Platform.isWindows then
    #[]
  else if System.Platform.isOSX then
    #["-I/opt/homebrew/opt/openblas/include"]
  else -- assuming linux
    #[]

package leanblas {
  moreLinkArgs := linkArgs
  preferReleaseBuild := true
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "9dbb163e576423ee953f0ee6f759f63714339162"

----------------------------------------------------------------------------------------------------
-- Build Lean ↔ BLAS bindings ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
target libleanblasc pkg : FilePath := do
  -- let openblas ← libopenblas.fetch
  -- pkg.afterBuildCacheAsync <| openblas.bindM fun d => do

  pkg.afterBuildCacheAsync do
    let mut oFiles : Array (Job FilePath) := #[]
    for file in (← (pkg.dir / "c").readDir) do
      if file.path.extension == some "c" then
        let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
        let srcJob ← inputTextFile file.path
        let weakArgs := #["-I", (← getLeanIncludeDir).toString]
        oFiles := oFiles.push (← buildO oFile srcJob weakArgs (#["-DNDEBUG", "-O3", "-fPIC"] ++ inclArgs) "gcc" getLeanTrace)
    let name := nameToStaticLib "leanblasc"

    buildStaticLib (pkg.sharedLibDir / name) (oFiles)

----------------------------------------------------------------------------------------------------

@[default_target]
lean_lib LeanBLAS where
  roots := #[`LeanBLAS]

lean_lib LeanBLAS.FFI where
  precompileModules := true
  moreLinkObjs := #[libleanblasc]

@[test_driver]
lean_exe ComprehensiveTests where
  root := `Test.TestRunner

lean_exe CBLASLevelOneTest where
  root := `Test.cblas_level_one

lean_exe DenseVectorTest where
  root := `Test.dense_vector

lean_exe TriangularTest where
  root := `Test.packed_triangular

lean_exe PropertyTests where
  root := `Test.Property

lean_exe EdgeCaseTests where
  root := `Test.EdgeCases

lean_exe BenchmarkTests where
  root := `Test.Benchmarks

lean_exe CorrectnessTests where
  root := `Test.Correctness

lean_exe Level3Tests where
  root := `Test.Level3

lean_exe SimpleTest where
  root := `Test.Simple

lean_exe BenchmarksFixedTest where
  root := `Test.BenchmarksFixed

-- Small utility executable used internally for measuring timings while
-- developing the benchmark suite.  Not part of the public API.
lean_exe TimeTest where
  root := `TimeTest

-- Public showcase executable
lean_exe Gallery where
  root := `Gallery

lean_exe Level3Benchmarks where
  root := `Test.BenchmarksLevel3

lean_exe PropertyDebugTest where
  root := `Test.PropertyDebug


-- ----------------------------------------------------------------------------------------------------
-- -- Download and build OpenBLAS ---------------------------------------------------------------------
-- -- -------------------------------------------------------------------------------------------------
-- -- This code was taken from: https://github.com/lean-dojo/LeanCopilot/blob/92a5ab6b58d06df8fd60d98dc38b1f674706eaad/lakefile.lean
-- ----------------------------------------------------------------------------------------------------

-- def nproc : IO Nat := do
--   let out ← IO.Process.output {cmd := "nproc", stdin := .null}
--   return min 1 ((out.stdout.trim.toNat? |>.getD 1) - 4)

-- private def nameToVersionedSharedLib (name : String) (v : String) : String :=
--   if Platform.isWindows then s!"{name}.dll"
--   else if Platform.isOSX  then s!"lib{name}.{v}.dylib"
--   else s!"lib{name}.so.{v}"

-- def afterReleaseAsync {α : Type} (pkg : Package) (build : JobM α) : FetchM (Job α) := do
--   if pkg.preferReleaseBuild ∧ pkg.name ≠ (← getRootPackage).name then
--     (← pkg.optGitHubRelease.fetch).mapM fun _ => build
--   else
--     Job.async build

-- def ensureDirExists (dir : FilePath) : IO Unit := do
--   if !(← dir.pathExists)  then
--     IO.FS.createDirAll dir

-- def gitClone (url : String) (cwd : Option FilePath) : LogIO Unit := do
--   proc (quiet := true) {
--     cmd := "git"
--     args := #["clone", "--recursive", url]
--     cwd := cwd
--   }

-- def getOpenBLASVersion (rootDir : FilePath) : LogIO String := do
--   -- Try to extract version from openblas_config.h after build
--   let configFile := rootDir / "openblas_config.h"
--   if ← configFile.pathExists then
--     let content ← IO.FS.readFile configFile
--     -- Look for #define OPENBLAS_VERSION " OpenBLAS x.y.z "
--     let lines := content.splitOn "\n"
--     for line in lines do
--       if line.contains "OPENBLAS_VERSION" && line.contains "define" then
--         -- Extract version from line like: #define OPENBLAS_VERSION " OpenBLAS 0.3.29 "
--         let parts := line.split (· == '"')
--         if parts.length ≥ 2 then
--           let versionStr := parts[1]!.trim
--           -- Remove "OpenBLAS " prefix if present
--           let version := if versionStr.startsWith "OpenBLAS " then
--             versionStr.drop 9
--           else
--             versionStr
--           return version.trim
--   -- Fallback: try to get version from Makefile.rule
--   let makefileRule := rootDir / "Makefile.rule"
--   if ← makefileRule.pathExists then
--     let content ← IO.FS.readFile makefileRule  
--     let lines := content.splitOn "\n"
--     for line in lines do
--       if line.startsWith "VERSION" && line.contains "=" then
--         let parts := line.split (· == '=')
--         if parts.length ≥ 2 then
--           return parts[1]!.trim
--   -- Default fallback
--   return "0.3"

-- target libopenblas pkg : FilePath := do
--   afterReleaseAsync pkg do
--     let rootDir := pkg.buildDir / "OpenBLAS"
--     ensureDirExists rootDir
--     let dst := pkg.sharedLibDir / (nameToSharedLib "openblas")
--     createParentDirs dst
--     let url := "https://github.com/OpenMathLib/OpenBLAS"

--     try
--       let depTrace := Hash.ofString url
--       setTrace depTrace
--       buildFileUnlessUpToDate' dst do
--         logInfo s!"Cloning OpenBLAS from {url}"
--         gitClone url pkg.buildDir

--         let numThreads := max 4 $ min 32 (← nproc)
--         let flags := #["NO_LAPACK=1", "NO_FORTRAN=1", s!"-j{numThreads}"]
--         logInfo s!"Building OpenBLAS with `make{flags.foldl (· ++ " " ++ ·) ""}`"
--         proc (quiet := true) {
--           cmd := "make"
--           args := flags
--           cwd := rootDir
--         }
--         proc {
--           cmd := "cp"
--           args := #[(rootDir / nameToSharedLib "openblas").toString, dst.toString]
--         }
--         -- Extract version from built OpenBLAS
--         let version ← getOpenBLASVersion rootDir
--         let dst' := pkg.sharedLibDir / (nameToVersionedSharedLib "openblas" version)
--         proc {
--           cmd := "cp"
--           args := #[dst.toString, dst'.toString]
--         }
--       let _ := (← getTrace)
--       return dst

--     else
--       proc {
--         cmd := "cp"
--         args := #[(rootDir / nameToSharedLib "openblas").toString, dst.toString]
--       }
--       -- Extract version from built OpenBLAS
--       let version ← getOpenBLASVersion rootDir
--       let dst' := pkg.sharedLibDir / (nameToVersionedSharedLib "openblas" version)
--       proc {
--         cmd := "cp"
--         args := #[dst.toString, dst'.toString]
--       }
--       addTrace <| ← computeTrace dst
--       return dst
