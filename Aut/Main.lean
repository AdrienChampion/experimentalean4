import Aut
import Aut.Acc

def main : IO Unit := do
  IO.println s!"I ♥ catz"
  IO.println ""
  Acc.run
  IO.println ""
  IO.println "done"
