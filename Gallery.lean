
/-!
## LeanBLAS Benchmark Gallery

`lake exe Gallery` is a convenient front-end that:

1. Runs the *fast* Level-1 benchmark set (`BenchmarksFixed`).
2. Runs the full benchmark suite (`BenchmarkTests`) for cache/scaling
   insights.

Nothing new is computed; we simply delegate to the existing `main` functions
and pretty-print a few section headers so the output is easy to scan.
-/

open IO Process

def runExe (cmd : String) (args : Array String := #[]) : IO Unit := do
  IO.println s!"--- running `{cmd} {String.intercalate " " args.toList}` ---"
  let out ← IO.Process.output {cmd := cmd, args := args, stdin := .null}
  IO.print out.stdout
  if out.exitCode ≠ 0 then
    IO.eprintln "(Executable returned non-zero status.)"

def main : IO Unit := do
  IO.println "================ LeanBLAS Benchmark Gallery ================"

  IO.println "\n(1) Quick sanity + performance check (BenchmarksFixed)\n"
  runExe "lake" #["exe", "BenchmarksFixedTest"]

  IO.println "\n(2) Full benchmark suite – cache & scaling analysis (BenchmarkTests)\n"
  runExe "lake" #["exe", "BenchmarkTests"]

  IO.println "\n(3) Level-3 GEMM benchmarks\n"
  runExe "lake" #["exe", "Level3Benchmarks"]

  IO.println "\n✓ Gallery run complete!"
