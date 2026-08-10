def maxOfInts (i j : Int) : Int :=
  if j ≤ i then i else j

def main : IO Unit := do
  let stdin ← IO.getStdin
  let line₁ ← stdin.getLine
  let line₂ ← stdin.getLine
  if let some i := line₁.trimAscii.toInt? then
    if let some j := line₂.trimAscii.toInt? then
      let k := maxOfInts i j
      IO.println s!"Max of {i} and {j} is {k}"

theorem le_maxOfInts_left {i j : Int} : i ≤ maxOfInts i j := by
  unfold maxOfInts
  omega

theorem le_maxOfInts_right {i j : Int} : j ≤ maxOfInts i j := by
  unfold maxOfInts
  omega

theorem maxOfInts_eq_left_or_eq_right {i j : Int} :
    maxOfInts i j = i ∨ maxOfInts i j = j := by
  unfold maxOfInts
  omega
