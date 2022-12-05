

def 𝕂 (val : α) : β → α :=
  fun _ => val


def Except.display (display : α → String) : Except String α → String
| .ok res => display res
| .error e => e
