def maxOfInts (i : Int) (j : Int) : Int :=
  if i >= j then i else j

def main : IO Unit := do
  let stdin <- IO.getStdin
  let line₁ <- stdin.getLine
  let line₂ <- stdin.getLine
  if let some i := line₁.trimAscii.toInt? then
  if let some j := line₂.trimAscii.toInt? then
  let k := maxOfInts i j
  IO.println s!"Max of {i} and {j} is {k}"

theorem max_ge_first : ∀ {i j : Int}, maxOfInts i j >= i := by
  unfold maxOfInts
  omega

theorem max_ge_second : ∀ {i j : Int}, maxOfInts i j >= j := by
  unfold maxOfInts
  omega

theorem max_is_first_or_second : ∀ {i j : Int}, maxOfInts i j = i ∨ maxOfInts i j = j := by
  unfold maxOfInts
  omega
