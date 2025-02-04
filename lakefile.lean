import Lake
open System Lake DSL

def linkArgs := #["-L/usr/lib/x86_64-linux-gnu/blas",
                  "-L/usr/lib/","-L/usr/local/lib","-lblas"]
def inclArgs : Array String := #[]

package leanblas {
  precompileModules := true
  moreLinkArgs := linkArgs
  moreLeancArgs := inclArgs
}

@[default_target]
lean_lib LeanBLAS where
  defaultFacets := #[LeanLib.sharedFacet,LeanLib.staticFacet]
  -- moreLinkArgs := linkArgs
  roots := #[`LeanBLAS]


@[test_driver]
lean_exe CBLASLevelOneTest where
  root := `Test.cblas_level_one
  -- moreLinkArgs := linkArgs

lean_exe DenseVectorTest where
  root := `Test.dense_vector
  -- moreLinkArgs := linkArgs

extern_lib libleanblasc pkg := do
  let mut oFiles : Array (BuildJob FilePath) := #[]
  for file in (← (pkg.dir / "c").readDir) do
    if file.path.extension == some "c" then
      let oFile := pkg.buildDir / "c" / (file.fileName.stripSuffix ".c" ++ ".o")
      let srcJob ← inputTextFile file.path
      let weakArgs := #["-I", (← getLeanIncludeDir).toString]
      oFiles := oFiles.push (← buildO oFile srcJob weakArgs (#["-DNDEBUG", "-O3", "-fPIC"] ++ inclArgs) "gcc" getLeanTrace)
  let name := nameToStaticLib "leanblasc"

  buildLeanSharedLib (pkg.nativeLibDir / name) oFiles
