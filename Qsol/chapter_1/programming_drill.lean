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

def subComplex (a b : Float × Float) : Float × Float :=
  (a.1 - b.1, a.2 - b.2)

def divComplex (a b : Float × Float) : Float × Float :=
  let denominator := b.1 * b.1 + b.2 * b.2
  ((a.1 * b.1 + a.2 * b.2) / denominator, (a.2 * b.1 - a.1 * b.2) / denominator)

def main_1_1_1 : IO Unit := do
  let a ← readComplex "first number"
  let b ← readComplex "second number"
  IO.print "Sum: "
  printComplex (sumComplex a b)
  IO.print "Product: "
  printComplex (productComplex a b)
  IO.print "Subtraction: "
  printComplex (subComplex a b)
  IO.print "Division: "
  if b.1 == 0 && b.2 == 0 then
    IO.println "Cannot divide by zero"
  else
    printComplex (divComplex a b)

def main_1_2_1 : IO Unit := do
  let x ← readComplex "complex number"
  IO.print "Conjugate: "
  printComplex (x.1, -x.2)
  IO.print "Modulus: "
  IO.println (Float.sqrt (x.1 * x.1 + x.2 * x.2))

def main_1_3_1_1 : IO Unit := do
  let x ← readComplex "complex number in Cartesian form"
  IO.print "Argument (radians): "
  IO.println (Float.atan2 x.2 x.1)
  IO.print "Argument (degrees): "
  IO.println (Float.atan2 x.2 x.1 * 180 / 3.141592653589793)
  IO.print "Magnitude: "
  IO.println (Float.sqrt (x.1 * x.1 + x.2 * x.2))

def main_1_3_1_2 : IO Unit := do
  let x ← readComplex "complex number in polar form"
  IO.print "Real part: "
  IO.println (x.1 * Float.cos x.2)
  IO.print "Imaginary part: "
  IO.println (x.1 * Float.sin x.2)
