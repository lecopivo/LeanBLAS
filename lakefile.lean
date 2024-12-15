import Lake
open System Lake DSL

package leanblast

def linkArgs := #["-lblas"]

@[default_target]
lean_lib LeanBLAS {
  defaultFacets := #[LeanLib.sharedFacet,LeanLib.staticFacet]
  moreLinkArgs := linkArgs
  roots := #[`LeanBLAS]
}

@[test_driver]
lean_exe Test {
  root := `Test.cblas_level_one
  moreLinkArgs := linkArgs
}


extern_lib libleanffi pkg := do
  let mut oFiles : Array (BuildJob FilePath) := #[]
  for file in (← (pkg.dir / "c").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString]
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace)
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) oFiles
