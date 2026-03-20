import Lean.Data.Json

def parseFloat (s : String) : IO Float :=
  match Lean.Json.parse s.trim with
  | .ok (.num n) => pure n.toFloat
  | _ => throw (IO.userError s!"Cannot parse '{s.trim}' as a number")

def readComplex (label : String) : IO (Float × Float) := do
  IO.print s!"Enter {label} real part: "
  let re ← parseFloat (← (← IO.getStdin).getLine)
  IO.print s!"Enter {label} imaginary part: "
  let im ← parseFloat (← (← IO.getStdin).getLine)
  return (re, im)

def sumComplex (a b : Float × Float) : Float × Float :=
  (a.1 + b.1, a.2 + b.2)

def productComplex (a b : Float × Float) : Float × Float :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)

def printComplex (z : Float × Float) : IO Unit :=
  let sign := if z.2 >= 0 then "+" else "-"
  IO.println s!"{z.1} {sign} {z.2.abs}i"

def main : IO Unit := do
  let a ← readComplex "first number"
  let b ← readComplex "second number"
  IO.print "Sum: "
  printComplex (sumComplex a b)
  IO.print "Product: "
  printComplex (productComplex a b)
