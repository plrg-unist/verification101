/--
An expression that evaluates to a natural number
e ::= n | x | e + e
-/
inductive NExpr where
  | num (n : Nat)
  | var (x : String)
  | add (e₁ e₂ : NExpr)

/--
An expression that evaluates to a boolean
b ::= e ≤ e
-/
inductive BExpr where
  | le (e₁ e₂ : NExpr)

/--
A command that updates a state
c ::= skip | x := e | c; c | if b then c else c | while b do c
-/
inductive Command where
  | skip
  | assign (x : String) (e : NExpr)
  | seq (c₁ c₂ : Command)
  | if_ (b : BExpr) (c₁ c₂ : Command)
  | while_ (b : BExpr) (c : Command)

/--
A state maps variables to natural numbers
-/
abbrev State : Type := String → Nat

/-- Updates a state to map a variable to a new value -/
def update (st : State) (x : String) (n : Nat) : State :=
  fun y ↦ if y == x then n else st y

/--
`NEval st e n` means `st ⊢ e ⇒ n`: under `st`, `e` evaluates to `n`.

-------------
 st ⊢ n ⇒ n

-----------------
 st ⊢ x ⇒ st(x)

 st ⊢ e₁ ⇒ n₁    st ⊢ e₂ ⇒ n₂
--------------------------------
    st ⊢ e₁ + e₂ ⇒ n₁ + n₂
-/
inductive NEval (st : State) : NExpr → Nat → Prop where
  | num {n : Nat} : NEval st (.num n) n
  | var {x : String} : NEval st (.var x) (st x)
  | add {e₁ e₂ : NExpr} {n₁ n₂ : Nat} :
      NEval st e₁ n₁ → NEval st e₂ n₂ → NEval st (.add e₁ e₂) (n₁ + n₂)

/-- Evaluates a natural-number expression under a state -/
def nEval (st : State) (e : NExpr) : Nat :=
  match e with
  | .num n => n
  | .var x => st x
  | .add e₁ e₂ => nEval st e₁ + nEval st e₂

theorem nEval_iff_nEval {st : State} {e : NExpr} {n : Nat} :
    NEval st e n ↔ nEval st e = n := by
  constructor
  · intro h
    induction h with
    | num => rfl
    | var => rfl
    | add _ _ ih₁ ih₂ => simp [nEval, ih₁, ih₂]
  · intro h
    subst n
    induction e with
    | num => exact .num
    | var => exact .var
    | add _ _ ih₁ ih₂ => exact .add ih₁ ih₂

/--
`BEval st b result` means `st ⊢ b ⇒ result`: under `st`, `b` evaluates to `result`.

 st ⊢ e₁ ⇒ n₁    st ⊢ e₂ ⇒ n₂
--------------------------------
    st ⊢ e₁ ≤ e₂ ⇒ n₁ ≤ n₂
-/
inductive BEval (st : State) : BExpr → Bool → Prop where
  | le {e₁ e₂ : NExpr} {n₁ n₂ : Nat} :
      NEval st e₁ n₁ → NEval st e₂ n₂ → BEval st (.le e₁ e₂) (n₁ ≤ n₂)

/-- Evaluates a boolean expression under a state -/
def bEval (st : State) (b : BExpr) : Bool :=
  match b with
  | .le e₁ e₂ => nEval st e₁ ≤ nEval st e₂

theorem bEval_iff_bEval {st : State} {b : BExpr} {result : Bool} :
    BEval st b result ↔ bEval st b = result := by
  constructor
  · intro h
    cases h with
    | le h₁ h₂ =>
      have ih₁ := nEval_iff_nEval.mp h₁
      have ih₂ := nEval_iff_nEval.mp h₂
      simp [bEval, ih₁, ih₂]
  · intro h
    cases b with
    | le e₁ e₂ =>
      simp only [bEval] at h
      subst result
      exact .le (nEval_iff_nEval.mpr rfl) (nEval_iff_nEval.mpr rfl)

/--
`CEval st c st'` means `st ⊢ c ⇒ st'`: `c` updates `st` to `st'`.

-----------------
 st ⊢ skip ⇒ st

       st ⊢ e ⇒ n
--------------------------
 st ⊢ x := e ⇒ st[x ↦ n]

 st₀ ⊢ c₁ ⇒ st₁    st₁ ⊢ c₂ ⇒ st₂
------------------------------------
       st₀ ⊢ c₁; c₂ ⇒ st₂

 st ⊢ b ⇒ true    st ⊢ c₁ ⇒ st'
----------------------------------
 st ⊢ if b then c₁ else c₂ ⇒ st'

 st ⊢ b ⇒ false    st ⊢ c₂ ⇒ st'
-----------------------------------
  st ⊢ if b then c₁ else c₂ ⇒ st'

 st₀ ⊢ b ⇒ true    st₀ ⊢ c ⇒ st₁    st₁ ⊢ while b do c ⇒ st₂
----------------------------------------------------------------
                   st₀ ⊢ while b do c ⇒ st₂

    st ⊢ b ⇒ false
-------------------------
 st ⊢ while b do c ⇒ st
-/
inductive CEval : State → Command → State → Prop where
  | skip {st : State} : CEval st .skip st
  | assign {st : State} {x : String} {e : NExpr} {n : Nat} :
      NEval st e n → CEval st (.assign x e) (update st x n)
  | seq {st₀ st₁ st₂ : State} {c₁ c₂ : Command} :
      CEval st₀ c₁ st₁ → CEval st₁ c₂ st₂ → CEval st₀ (.seq c₁ c₂) st₂
  | if_true {st st' : State} {b : BExpr} {c₁ c₂ : Command} :
      BEval st b true → CEval st c₁ st' → CEval st (.if_ b c₁ c₂) st'
  | if_false {st st' : State} {b : BExpr} {c₁ c₂ : Command} :
      BEval st b false → CEval st c₂ st' → CEval st (.if_ b c₁ c₂) st'
  | while_true {st₀ st₁ st₂ : State} {b : BExpr} {c : Command} :
      BEval st₀ b true → CEval st₀ c st₁ → CEval st₁ (.while_ b c) st₂ →
        CEval st₀ (.while_ b c) st₂
  | while_false {st : State} {b : BExpr} {c : Command} :
      BEval st b false → CEval st (.while_ b c) st

/--
i := 0;
sum := 0;
while i ≤ n do
  sum := sum + i;
  i := i + 1
-/
def sumCommand : Command :=
  .seq
    (.assign "i" (.num 0))
    (.seq
      (.assign "sum" (.num 0))
      (.while_ (.le (.var "i") (.var "n"))
        (.seq
          (.assign "sum" (.add (.var "sum") (.var "i")))
          (.assign "i" (.add (.var "i") (.num 1))))))

/-- `SumFromZero n n'` states that the sum from `0` to `n` is `n'` -/
inductive SumFromZero : Nat → Nat → Prop where
  | zero : SumFromZero 0 0
  | succ {n sum : Nat} : SumFromZero n sum → SumFromZero (n + 1) (sum + (n + 1))

theorem sumCommand_computes_sum {st st' : State} (h : CEval st sumCommand st') :
    SumFromZero (st "n") (st' "sum") := by
  sorry
