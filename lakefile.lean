import Lake

open Lake DSL System Lean Elab

package leanblas {
  precompileModules := true
}

@[default_target]
lean_lib LeanBLAS where
  defaultFacets := #[LeanLib.sharedFacet,LeanLib.staticFacet]
  roots := #[`LeanBLAS]

@[test_driver]
lean_exe CBLASLevelOneTest where
  root := `Test.cblas_level_one

lean_exe DenseVectorTest where
  root := `Test.dense_vector

lean_exe TriangularTest where
  root := `Test.packed_triangular

----------------------------------------------------------------------------------------------------
-- Download and build OpenBLAS ---------------------------------------------------------------------
-- --------------------------------------------------------------------------------------------------
-- This code was taken from: https://github.com/lean-dojo/LeanCopilot/blob/92a5ab6b58d06df8fd60d98dc38b1f674706eaad/lakefile.lean
----------------------------------------------------------------------------------------------------

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trim.toNat? |>.getD 1

private def nameToVersionedSharedLib (name : String) (v : String) : String :=
  if Platform.isWindows then s!"{name}.dll"
  else if Platform.isOSX  then s!"lib{name}.{v}.dylib"
  else s!"lib{name}.so.{v}"

def afterReleaseAsync {α : Type} (pkg : Package) (build : JobM α) : FetchM (Job α) := do
  if pkg.preferReleaseBuild ∧ pkg.name ≠ (← getRootPackage).name then
    (← pkg.optGitHubRelease.fetch).mapM fun _ => build
  else
    Job.async build

def ensureDirExists (dir : FilePath) : IO Unit := do
  if !(← dir.pathExists)  then
    IO.FS.createDirAll dir

def gitClone (url : String) (cwd : Option FilePath) : LogIO Unit := do
  proc (quiet := true) {
    cmd := "git"
    args := #["clone", "--recursive", url]
    cwd := cwd
  }

target libopenblas pkg : FilePath := do
  afterReleaseAsync pkg do
    let rootDir := pkg.buildDir / "OpenBLAS"
    ensureDirExists rootDir
    let dst := pkg.nativeLibDir / (nameToSharedLib "openblas")
    createParentDirs dst
    let url := "https://github.com/OpenMathLib/OpenBLAS"

    try
      let depTrace := Hash.ofString url
      setTrace depTrace
      buildFileUnlessUpToDate' dst do
        logInfo s!"Cloning OpenBLAS from {url}"
        gitClone url pkg.buildDir

        let numThreads := max 4 $ min 32 (← nproc)
        let flags := #["NO_LAPACK=1", "NO_FORTRAN=1", s!"-j{numThreads}"]
        logInfo s!"Building OpenBLAS with `make{flags.foldl (· ++ " " ++ ·) ""}`"
        proc (quiet := true) {
          cmd := "make"
          args := flags
          cwd := rootDir
        }
        proc {
          cmd := "cp"
          args := #[(rootDir / nameToSharedLib "openblas").toString, dst.toString]
        }
        -- TODO: Don't hardcode the version "0".
        let dst' := pkg.nativeLibDir / (nameToVersionedSharedLib "openblas" "0")
        proc {
          cmd := "cp"
          args := #[dst.toString, dst'.toString]
        }
      let _ := (← getTrace)
      return dst

    else
      addTrace <| ← computeTrace dst
      return dst


----------------------------------------------------------------------------------------------------
-- Build Lean ↔ BLAS bindings ---------------------------------------------------------------------
----------------------------------------------------------------------------------------------------

extern_lib libleanblasc pkg := do
  let openblas ← libopenblas.fetch
  let _ ← openblas.await
  let inclArgs := #[s!"-I{pkg.lakeDir / "build" / "OpenBLAS"}"]

  let mut oFiles : Array (Job FilePath) := #[]
  for file in (← (pkg.dir / "c").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString]
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs (#["-DNDEBUG", "-O3", "-fPIC"] ++ inclArgs) "gcc" getLeanTrace)
  let name := nameToStaticLib "leanblasc"

  buildLeanSharedLib (pkg.nativeLibDir / name) (oFiles.push openblas)
