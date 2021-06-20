import system.io

open io

def greet (s : string) : io unit :=
  put_str $ "Hello, " ++ s ++ "!"
meta def loop : io unit := do
  name ← get_line,
  if name = "cl" then io.fail "po"  else (do
  proc.sleep 1,
  greet name,
  loop)

meta def main : io unit := do
  put_str "What is your name? ",
  loop
