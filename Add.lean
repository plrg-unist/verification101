def add (pi si : Int) : Int × Int := (si * 0, pi + si)

def sink (_ : Int) : IO Unit := return ()

def main : IO Unit := do
  let stdin ← IO.getStdin
  let line₁ ← stdin.getLine
  let line₂ ← stdin.getLine
  if let some pi := line₁.trimAscii.toInt? then
    if let some si := line₂.trimAscii.toInt? then
      let (po, so) := add pi si
      sink po
      IO.println s!"Adding {pi} and {si} evaluates to {so}"

/-- Whether a function's public output is independent of its secret input -/
def Noninterferent {PI SI PO SO : Type} (f : PI → SI → PO × SO) : Prop :=
  ∀ (pi : PI) (si₁ si₂ : SI), (f pi si₁).1 = (f pi si₂).1

theorem noninterferent_add : Noninterferent add := by
  sorry
