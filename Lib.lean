/-! Eval -/
-- use "#eval" to evaluate a term

#eval 1 + 2
#eval -1 + 2
#eval 1.1 + 2.2
#eval true && false
#eval 'x'
#eval "Hello, world!"

/-! Check -/
-- use "#check" to type-check a term

#check 1 + 2
#check -1 + 2
#check 1.1 + 2.2
#check true && false
#check 'x'
#check "Hello, world!"

/-! Functions -/
-- Functions are introduced using "def"

/-- Doubles a natural number -/
def double (n : Nat) : Nat := n + n

#eval double 2
#eval double (2 + 3)

#check double
#check @double

/-- Adds two natural numbers -/
def add (n : Nat) (m : Nat) : Nat := n + m

#eval add 1 2
#eval add (1 + 2) 3
#eval add 1 (2 + 3)

#check @add

#eval (add 1) 2

/-- Adds 1 to a natural number -/
def add1 : Nat → Nat := add 1
-- def add1 : Nat -> Nat := add 1

#eval add1 2

/-- Adds two natural numbers -/
def add' (n m : Nat) : Nat := n + m

#check @add'

/-- Natural number 1 -/
def one : Nat := 1

#eval one

/-! Anonymous Functions -/
-- Anonymous functions are introduced using "fun"

/-- Adds two natural numbers -/
def add'' : Nat → Nat → Nat := fun n ↦ fun m ↦ n + m
-- def add'' : Nat -> Nat -> Nat := fun n => fun m => n + m

#eval add'' 1 2

#check add''

/-- Adds two natural numbers -/
def add''' : Nat → Nat → Nat := fun n m ↦ n + m

/-- Applies a function twice -/
def twice (f : Nat → Nat) (n : Nat) := f (f n)

#check @twice
#eval twice double 2
#eval twice (fun n ↦ n + n) 2
#eval twice (add 1) 3
#eval twice (fun n ↦ n + 1) 3
#eval (fun n ↦ n + n) (1 + 2)

/-! Local Definitions -/

/-- Triples a natural number -/
def triple (n : Nat) : Nat :=
  let m := n + n
  n + m

#eval triple 2

/-- Quadruples a natural number -/
def quadruple (n : Nat) : Nat :=
  let double (n : Nat) : Nat := n + n
  double (double n)

#eval quadruple 2

/-! Inductive Types -/
-- Inductive types are introduced using "inductive" and eliminated using "match"

/-- A day of week -/
inductive Day : Type where
  | monday : Day
  | tuesday : Day
  | wednesday : Day
  | thursday : Day
  | friday : Day
  | saturday : Day
  | sunday : Day

/-
In C,
enum Day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };
-/

#eval Day.monday
#check Day.monday

-- ": Type" and ": <type>" can be usually omitted
/-- A day of week -/
inductive Day' where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday

/-- The next day of a day -/
def nextDay (d : Day) : Day :=
  match d with
  | Day.monday => Day.tuesday
  | Day.tuesday => Day.wednesday
  | Day.wednesday => Day.thursday
  | Day.thursday => Day.friday
  | Day.friday => Day.saturday
  | Day.saturday => Day.sunday
  | Day.sunday => Day.monday

#check @nextDay
#eval nextDay Day.monday

-- The type name can be omitted if it is clear from the context
/-- The next day of a day -/
def nextDay' (d : Day) : Day :=
  match d with
  | .monday => .tuesday
  | .tuesday => .wednesday
  | .wednesday => .thursday
  | .thursday => .friday
  | .friday => .saturday
  | .saturday => .sunday
  | .sunday => .monday

#eval nextDay' Day.monday

/-- A shape that is either a rectangle or a circle -/
inductive Shape where
  | rectangle (w h : Nat)
  | circle (r : Nat)

/-
In Java,
abstract class Shape {}
class Rectangle extends Shape { int w; int h; }
class Circle extends Shape { int r; }
-/

#eval Shape.rectangle 1 2
#check Shape.rectangle 1 2
#check @Shape.rectangle
#check Shape.rectangle 1

/-- The area of a shape -/
def area (s : Shape) : Nat :=
  match s with
  | .rectangle w h => w * h
  | .circle r => 3 * r * r

#eval area (.rectangle 2 3)
#eval area (.circle 2)

-- The name of a binding doesn't matter
/-- The area of a shape -/
def area' (s : Shape) : Nat :=
  match s with
  | .rectangle x y => x * y
  | .circle x => 3 * x * x

-- A variant can be defined without giving a name to its parameter
/-- A shape that is either a rectangle or a circle -/
inductive Shape' where
  | rectangle : Nat -> Nat -> Shape'
  | circle : Nat -> Shape'

-- A type may have only a single variant
/-- A point in a 2-dimensional plain -/
inductive Point where
  | intro (x y : Nat)

/-- A mid-point between two points -/
def midpoint (p₁ p₂ : Point) : Point :=
  match p₁, p₂ with
  | .intro x₁ y₁, .intro x₂ y₂ => .intro ((x₁ + x₂) / 2) ((y₁ + y₂) / 2)

#eval midpoint (.intro 2 3) (.intro 4 7)

/-- A mid-point between two points -/
def midpoint' (p₁ p₂ : Point) : Point :=
  let ⟨ x₁, y₁ ⟩ := p₁
  let ⟨ x₂, y₂ ⟩ := p₂
  ⟨ (x₁ + x₂) / 2, (y₁ + y₂) / 2 ⟩

#eval midpoint' ⟨ 2, 3 ⟩ ⟨ 4, 7 ⟩

-- A structure is a single-variant inductive type with some syntactic sugar
/-- A point in a 2-dimensional plain -/
structure Point' where
  x : Nat
  y : Nat

/-! Recursion -/
-- Inductive types and functions can be recursive

/-- A natural number -/
inductive MyNat where
  /-- 0 is a natural number -/
  | zero
  /-- A successor of a natural number is also a natural number -/
  | succ (n : MyNat)

#eval MyNat.zero -- 0
#eval MyNat.succ (.zero) -- 1
#eval MyNat.succ (.succ (.zero)) -- 2
#eval MyNat.succ (.succ (.succ (.zero))) -- 3

#check MyNat.zero -- 0
#check MyNat.succ (.zero) -- 1
#check MyNat.succ (.succ (.zero)) -- 2
#check MyNat.succ (.succ (.succ (.zero))) -- 3

/-- Adds two natural number -/
def myAdd (n m : MyNat) : MyNat :=
  match m with
  | .zero => n
  | .succ m' => .succ (myAdd n m')

#check Nat.add

#eval myAdd (.succ .zero) (.succ (.succ .zero)) -- 1 + 2

-- "Nat" is defined in the same way
/-
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-/

#eval Nat.succ (.succ (.succ .zero))

/-- The sum from zero to a natural number -/
def sumFromZero (n : Nat) : Nat :=
  match n with
  | .zero => 0
  | .succ n' => n + sumFromZero n'

#eval sumFromZero 10

/-- Sum from zero to a natural number -/
def sumFromZero' (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => n + sumFromZero n'

#eval sumFromZero' 10

/-- A list of natural numbers -/
inductive NatList where
  /-- The empty list -/
  | nil
  /-- A pair of a natural number and a list -/
  | cons (h : Nat) (t : NatList)

#eval NatList.nil -- []
#eval NatList.cons 0 .nil -- [0]
#eval NatList.cons 0 (.cons 1 .nil) -- [0, 1]

/-- The sum of natural numbers in a list -/
def sumOfNats (ns : NatList) : Nat :=
  match ns with
  | .nil => 0
  | .cons h t => h + sumOfNats t

#eval sumOfNats (.cons 1 (.cons 2 (.cons 3 .nil)))

/-! Polymorphism -/
-- Parametric polymorphism, a.k.a, generics

/-- A list of elements of type α -/
inductive MyList (α : Type) where
  /-- The empty list -/
  | nil
  /-- A pair of an element and a list -/
  | cons (h : α) (t : MyList α)

#check MyList.cons 0 (.cons 1 .nil) -- [0, 1]
#check MyList.cons false (.cons true .nil) -- [false, true]

/-- Appends a list to another list -/
def myAppend (α : Type) (xs ys : MyList α) : MyList α :=
  match xs with
  | .nil => ys
  | .cons h t => .cons h (myAppend α t ys)

#check @myAppend
#eval myAppend Nat (.cons 0 .nil) (.cons 1 .nil)
#eval myAppend Bool (.cons false .nil) (.cons true .nil)

-- Parameters in curly braces are inferred
/-- Appends a list to another list -/
def myAppend' {α : Type} (xs ys : MyList α) : MyList α :=
  match xs with
  | .nil => ys
  | .cons h t => .cons h (myAppend' t ys)

#check @myAppend'
#eval myAppend' (.cons 0 .nil) (.cons 1 .nil)
#eval myAppend' (.cons false .nil) (.cons true .nil)

#check List

-- "List" is defined in the same way
/-
inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
-/

#eval List.cons 0 (.cons 1 (.cons 2 .nil))
#eval [0, 1, 2]

/-- Appends a list to another list -/
def append {α : Type} (xs ys : List α) : List α :=
  match xs with
  | .nil => ys
  | .cons h t => .cons h (append t ys)

/-- Appends a list to another list -/
def append' {α : Type} (xs ys : List α) : List α :=
  match xs with
  | [] => ys
  | h :: t => .cons h (append t ys)

/-! Generalized Algebraic Data Types (GADTs) -/
-- Polymorphic types may have variants that can be only instantiated with specific types

/-- An expression of Expr α evaluates to a value of α -/
inductive Expr : Type -> Type where
  | num (n : Nat) : Expr Nat
  | add (l r : Expr Nat) : Expr Nat
  | lt (l r : Expr Nat) : Expr Bool
  | and (l r : Expr Bool) : Expr Bool

#check Expr.num 1
#check Expr.add (.num 1) (.num 2)
#check Expr.lt (.num 1) (.num 2)
#check Expr.and (.lt (.num 1) (.num 2)) (.lt (.num 3) (.num 4))

/-- Evaluates an expression -/
def evalExpr {α : Type} (e : Expr α) : α :=
  match e with
  | .num n => n
  | .add l r => evalExpr l + evalExpr r
  | .lt l r => evalExpr l < evalExpr r
  | .and l r => evalExpr l && evalExpr r

#check evalExpr (.num 1)
#check evalExpr (.lt (.num 1) (.num 2))

/-! Dependent Types -/
-- Abstracting a type with a term

#check fun n => n + 1
#check @myAppend
#check @MyList

/-
     | Term     | Type
-----+----------+----------------------
Term | Function | Polymorphic function
Type | ???      | Polymorphic type
-/

#check @Vector

/-- MyVector α n is a vector of n elements of type α -/
inductive MyVector (α : Type) : Nat -> Type where
  /-- The empty vector -/
  | nil : MyVector α 0
  /-- A pair of an element and a vector -/
  | cons {n : Nat} (h : α) (t : MyVector α n) : MyVector α (n + 1)

#check @MyVector
#check MyVector Int
#check MyVector Bool

/-
     | Term           | Type
-----+----------------+----------------------
Term | Function       | Polymorphic function
Type | Dependent type | Polymorphic type
-/

#check MyVector.nil
#check MyVector.cons 0 .nil
#check MyVector.cons 0 (.cons 1 .nil)
#check MyVector.cons 0 (.cons 1 (.cons 2 .nil))

-- A dependent function is a function whose return type depends on its parameter
/-- Makes a vector with n copies of x -/
def makeVector {α : Type} (x : α) (n : Nat) : MyVector α n :=
  match n with
  | 0 => .nil
  | n' + 1 => .cons x (makeVector x n')

#check @makeVector

#check makeVector 2 3
#eval makeVector 2 3

#check makeVector true 2
#eval makeVector true 2

def appendVector {α : Type} {n m : Nat} (xs : MyVector α n) (ys : MyVector α m) : MyVector α (m + n) :=
  match xs with
  | .nil => ys
  | .cons h t => .cons h (appendVector t ys)

#check appendVector (makeVector 1 2) (makeVector 2 3)

/-- A greeting message in string or character list -/
def greeting (useString : Bool) : if useString then String else List Char :=
  match useString with
  | true => "Hello, world!"
  | false => ['H', 'e', 'l', 'l', 'o', ',', ' ', 'w', 'o', 'r', 'l', 'd', '!']

#check @greeting
#check greeting true
#eval (greeting true : String)
#check greeting false
#eval (greeting false : List Char)

-- A dependent pair is a pair whose second element's type depends on the first element
/-- A school class -/
inductive Class where
  | intro (n : Nat) (students : MyVector String n)

#check Class.intro 1 (.cons "Alice" .nil)

/-- Merges two classes -/
def mergeClasses (c₁ c₂ : Class) : Class :=
  let ⟨ n₁, students₁ ⟩ := c₁
  let ⟨ n₂, students₂ ⟩ := c₂
  ⟨ n₂ + n₁, appendVector students₁ students₂ ⟩

#check mergeClasses
  ⟨ 1, (.cons "Alice" .nil) ⟩
  ⟨ 2, (.cons "Bob" (.cons "Charlie" .nil)) ⟩

/-! Propositions -/
-- A proposition is a statement that is true or false

/-
* Monday is weekend: False
* Tuesday is weekend: False
* Wednesday is weekend: False
* Thursday is weekend: False
* Friday is weekend: False
* Saturday is weekend: True
* Sunday is weekend: True
-/

/-
We introduce two inference rules:

---------------------
 Saturday is weekend

-------------------
 Sunday is weekend
-/

/-
Curry-Howard correspondence:
* A proposition is a type
* A proof is a term
* Checking a proof is type checking
-/

/-- Whether a day is weekend -/
inductive Weekend : Day -> Prop where
  /-- Saturday is weekend -/
  | saturday : Weekend .saturday
  /-- Sunday is weekend -/
  | sunday : Weekend .sunday

theorem saturday_is_weekend : Weekend .saturday := .saturday
theorem sunday_is_weekend : Weekend .sunday := .sunday

/-
Alice goes to a party on Wednesday
Bob goes to a party on weekends
Bob goes to a party when Alice does

We introduce three inference rules:

------------------------------------
 Alice goes to a party on Wednesday

      [d] is weekend
----------------------------
 Bob goes to a party on [d]

 Alice goes to a party on [d]
------------------------------
  Bob goes to a party on [d]
-/

/-- A person (Alice, Bob, or Charlie) -/
inductive Person where
  | alice
  | bob
  | charlie

/-- Whether a certain person goes to a party on a certain day -/
inductive Party : Person -> Day -> Prop where
  | alice : Party .alice .wednesday
  | bobLikesWeekend {d : Day} (h : Weekend d) : Party .bob d
  | bobLikesAlice {d : Day} (h : Party .alice d) : Party .bob d

-- Not giving any name to a proof parameter usually looks more natural
/-- Whether a certain person goes to a party on a certain day -/
inductive Party' : Person -> Day -> Prop where
  | alice : Party' .alice .wednesday
  | bobLikesWeekend {d : Day} : Weekend d -> Party' .bob d
  | bobLikesAlice {d : Day} : Party .alice d -> Party' .bob d

theorem alice_goes_to_a_party_on_wednesday : Party .alice .wednesday := .alice
theorem bob_goes_to_a_party_on_saturday : Party .bob .saturday := .bobLikesWeekend .saturday
theorem bob_goes_to_a_party_on_sunday : Party .bob .sunday := .bobLikesWeekend .sunday
theorem bob_goes_to_a_party_on_wednesday : Party .bob .wednesday := .bobLikesAlice .alice

-- Logical implication is a function
theorem modus_ponens (a b : Prop) (ha : a) (hab : a → b) : b := hab ha
theorem modus_ponens' : (a b : Prop) → a → (a → b) → b := fun _ _ ha hab ↦ hab ha

-- Universal quantification is a dependent function
theorem modus_ponens'' : forall (a b : Prop), a → (a → b) → b := fun _ _ ha hab ↦ hab ha
theorem modus_ponens''' : forall {a b : Prop}, a → (a → b) → b := fun ha hab ↦ hab ha

-- Logical conjunction is defined as an inductive proposition (actually structure)
/-
inductive And (a b : Prop) : Prop where
  | intro (left : a) (right : b)
-/

#check @And

theorem a_b_then_a_and_b : ∀ {a b : Prop}, a → b → a ∧ b := fun ha hb ↦ ⟨ ha, hb ⟩
theorem a_and_b_then_a : ∀ {a b : Prop}, a ∧ b → a := fun ⟨ ha, _ ⟩ ↦ ha
theorem a_and_b_then_b : ∀ {a b : Prop}, a ∧ b → b := fun ⟨ _, hb ⟩ ↦ hb

-- Logical disjunction is defined as an inductive proposition
/-
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

#check @Or

theorem a_then_a_or_b : ∀ {a b : Prop}, a → a ∨ b := .inl
theorem b_then_a_or_b : ∀ {a b : Prop}, b → a ∨ b := .inr

-- Existential quantification is a dependent pair
/-
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
-/
#check @Exists

theorem alice_goes_to_a_party : Exists (fun d ↦ Party .alice d) :=
  ⟨ .wednesday, .alice ⟩

theorem alice_goes_to_a_party' : ∃ (d : Day), Party .alice d :=
  ⟨ .wednesday, .alice ⟩

-- Tautology is defined as an inductive proposition
/-
inductive True : Prop where
  | intro : True
-/

#check True

theorem true_holds : True := .intro

-- Contradiction is defined as an inductive proposition
/-
inductive False : Prop
-/

#check False

-- ¬ P is defined as P → False
theorem monday_is_not_weekend : Weekend .monday → False := fun h ↦ nomatch h
theorem monday_is_not_weekend' : ¬ Weekend .monday := nofun
theorem false_does_not_hold : ¬ False := nofun

-- Equality is defined as an inductive proposition
/-
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
-/

#check @Eq

theorem one_is_one : Eq 1 1 := .refl 1
theorem one_is_one' : 1 = 1 := rfl

#check @rfl

theorem one_is_one_plus_zero : 1 = 1 + 0 := .refl 1
theorem one_is_one_plus_zero' : 1 = 1 + 0 := .refl (1 + 0)

theorem zero_is_not_one : ¬ 0 = 1 := nofun
theorem zero_is_not_one' : 0 ≠ 1 := nofun

theorem n_is_n_plus_zero : ∀ {n : Nat}, n = n + 0 := rfl

/-
def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
-/

-- theorem n_is_zero_plus_n : ∀ {n : Nat}, n = 0 + n := rfl

theorem day_on_which_alice_goes_to_a_party_is_wednesday :
    ∀ {d : Day}, Party .alice d -> d = .wednesday :=
  fun h ↦
    match h with
    | .alice => rfl

/-- Tactics -/

theorem saturday_is_weekend' : Weekend .saturday := by
  apply Weekend.saturday

#print saturday_is_weekend'

theorem sunday_is_weekend' : Weekend .sunday := by
  apply Weekend.sunday

theorem alice_goes_to_a_party_on_wednesday' : Party .alice .wednesday := by
  apply Party.alice

theorem bob_goes_to_a_party_on_saturday' : Party .bob .saturday := by
  apply Party.bobLikesWeekend
  apply Weekend.saturday

#print bob_goes_to_a_party_on_saturday'

theorem bob_goes_to_a_party_on_sunday' : Party .bob .sunday := by
  apply Party.bobLikesWeekend
  apply Weekend.sunday

theorem bob_goes_to_a_party_on_wednesday' : Party .bob .wednesday := by
  apply Party.bobLikesAlice
  apply Party.alice

theorem modus_ponens'''' : forall {a b : Prop}, a → (a → b) → b := by
  intros a b ha hab
  apply hab
  apply ha

#print modus_ponens''''

theorem a_b_then_a_and_b' : ∀ {a b : Prop}, a → b → a ∧ b := by
  intros a b ha hb
  apply And.intro
  { apply ha }
  { apply hb }

#print a_b_then_a_and_b'

theorem a_and_b_then_a' : ∀ {a b : Prop}, a ∧ b → a := by
  intros a b hab
  cases hab with
  | intro ha _ => apply ha

#print a_and_b_then_a'

theorem a_then_a_or_b' : ∀ {a b : Prop}, a → a ∨ b := by
  intros a b ha
  apply Or.inl
  apply ha

theorem b_then_a_or_b' : ∀ {a b : Prop}, b → a ∨ b := by
  intros a b hb
  apply Or.inr
  apply hb

theorem alice_goes_to_a_party'' : ∃ (d : Day), Party .alice d := by
  exists .wednesday
  apply Party.alice

theorem monday_is_not_weekend'' : ¬ Weekend .monday := by
  intro h
  cases h

theorem n_is_n_plus_zero' : ∀ {n : Nat}, n = n + 0 := by
  intro n
  rfl

theorem zero_plus_succ_n_is_succ_zero_plus_n :
    ∀ {n : Nat}, 0 + Nat.succ n = Nat.succ (0 + n) := by
  intro n
  rfl

theorem n_is_zero_plus_n : ∀ {n : Nat}, n = 0 + n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    rewrite [zero_plus_succ_n_is_succ_zero_plus_n]
    rewrite [<- ih]
    rfl

#print n_is_zero_plus_n
#check @Nat.rec
/-
Nat.rec :
  (p : Nat → Prop) →
  p 0 →
  (∀ (n : Nat), p n → p (.succ n)) →
  (∀ (n : Nat), p n)
-/

#check @NatList.rec
/-
NatList.rec :
  (p : NatList → Prop) →
  (p .nil) →
  (∀ (h : Nat) (t : NatList), p t → p (.cons h t)) →
  (∀ (ns : NatList), p ns)
-/

/-
def List.length : List α → Nat
  | nil       => 0
  | cons _ as => HAdd.hAdd (length as) 1

def List.append : (xs ys : List α) → List α
  | nil,       bs => bs
  | cons a as, bs => cons a (List.append as bs)
-/

theorem length_of_appended_list_is_sum_of_lengths {α : Type} :
  ∀ (xs ys : List α), List.length (List.append xs ys) = List.length xs + List.length ys := by
  intros xs ys
  induction xs with
  | nil => simp
  | cons h t ih => simp; omega

/- ((h :: t).append ys).length
 = (h :: (t.append ys)).length  (by the definition of append)
 = (t.append ys).length + 1  (by the definition of length)
 = (t.length + ys.length) + 1  (by the induction hypothesis)
-/
/- (h :: t).length + ys.length
 = (t.length + 1) + ys.length  (by the definition of length)
-/
