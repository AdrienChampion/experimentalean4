import Cla

def main (args : List String) : IO Unit :=
  do
    IO.println s!"lif sux"
    for arg in args do
      IO.println s!"arg : {arg}"
