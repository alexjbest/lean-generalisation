import data.list.basic
import system.io
import tactic

#check _root_.trace
def a : ℕ := trace "hi" (1+1)
#eval a
open tactic
#check char_buffer
def parcmd (args : io.process.spawn_args) : io unit :=
do
  a ← (list.range 2).mmap $ λ i, io.proc.spawn { stdout := io.process.stdio.piped, stdin := io.process.stdio.piped, ..args },
  (list.range 4).mmap $ λ i, io.fs.put_str_ln (a.nth_le (i % 2) (sorry)).stdin (to_string i),
  a.mmap $ λ i, io.fs.put_str_ln i.stdin "cl",
  a.mmap $ λ i : io.proc.child, (do io.fs.close i.stdin,
  buf ← io.fs.read_to_end i.stdout,
  trace buf.to_string
  io.fs.close i.stdout,
  exitv ← io.proc.wait i,
  when (exitv ≠ 0) $ io.fail $ "process exited with status " ++ repr exitv),
  io.fail  "a"
-- run_cmd do trace $ tactic.unsafe_run_io $ parcmd { cmd := "lean.exe",
--   args := ["--run", "src/dumb.lean"]
--   -- stdin := _
--   -- stdout := _,
--   -- stderr := _,
--   -- cwd := "",
--   -- env := _
--   }
