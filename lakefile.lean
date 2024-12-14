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


lean_exe Main {
  root := `Main
  supportInterpreter := true
  moreLinkArgs := linkArgs
}


target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "levelone.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "gcc" getLeanTrace


extern_lib libleanffi pkg := do
  let ffiO ← ffi.o.fetch
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]
