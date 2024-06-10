def hello := "world"

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check types. -/

#check m            -- output: Nat
#check m * (n + 0)  -- Nat
#check b1 && b2     -- "&&" is the Boolean and
#check Nat
#check Type
#check Type 2

/- Evaluate -/

#eval m + 2         -- 3
#eval b1 && b2      -- false

/- Define Functions -/

def func (x y : Nat) (b : Bool) : Nat :=
  if b then x + y + 2 else 0

def func_2 : Nat -> Nat -> Bool -> Nat :=
  func

def func₂ : Nat → Nat → Bool → Nat :=
  λ x y => λ b => if b then x + y + 2 else 0

#check func
#check func_2
#check func₂
#eval func 1 2 true

def simple_statement : func 1 2 true = 5 := rfl

#check simple_statement
#check func 1 2 true = 5


/- Products -/

def α : Type := Nat
def β : Type := Bool

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

/- Lists -/

#check List

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α
#check List.cons            -- (α : Type) → α → List α → List α


/- Propositions and Proofs -/

variable {p : Prop}
variable {q : Prop}
variable {r : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1

#check t1 simple_statement simple_statement

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

example (h : p ∧ q) : q ∧ p :=
  And.intro h.right h.left

example (h : p ∧ q) : q ∧ p :=
  match h with
  | And.intro a b => And.intro b a


example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp => hnq (hpq hp)

example (hpq : p → q) (hnq : ¬q) (hp : p): False :=
  hnq (hpq hp)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry


/- Quantifiers -/

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left


variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example : ∃ x : Nat, x > 0 :=
  ⟨1, (Nat.zero_lt_succ 0)⟩

variable (α : Type) (P Q : α → Prop)

example (h : ∃ x, P x ∧ Q x) : ∃ x, Q x ∧ P x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) := sorry
example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) := sorry
example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := sorry


/- Tactics -/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

/- Inductive Types -/

inductive N where
  | zero : N
  | succ : N → N
  deriving Repr

#check @N.rec

def addN (m n : N) : N :=
  match n with
  | N.zero   => m
  | N.succ n => N.succ (addN m n)

#eval addN (N.succ (N.succ N.zero)) (N.succ N.zero)

theorem add_zero (m : N) : addN m N.zero = m := rfl

theorem add_succ (m n : N) : addN m (N.succ n) = N.succ (addN m n) := rfl

instance : Add N where
  add := addN

theorem zero_add (n : N) : N.zero + n = n :=
  N.recOn (motive := fun x => N.zero + x = x)
   n
   (show N.zero + N.zero = N.zero from rfl)
   (fun (n : N) (ih : N.zero + n = n) =>
    show N.zero + N.succ n = N.succ n from
    calc N.zero + N.succ n
      _ = N.succ (N.zero + n) := rfl
      _ = N.succ n       := by rw [ih])

theorem zero_add₂ (n : N) : N.zero + n = n :=
  match n with
  | N.zero => rfl
  | N.succ x => congrArg N.succ (zero_add₂ x)

#print congrArg

inductive L (α : Type) where
  | nil : L α
  | cons : α → L α → L α

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

structure Point (α : Type) where
  x : α
  y : α
deriving Repr

def myPt : Point N := { x := N.zero, y := N.zero }

def anotherPt : Point N := {myPt with x := N.succ N.zero}

/- Algebra -/

class Group (α : Type u) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  mul_left_inv : ∀ x : α, mul (inv x) x = one

inductive Z2 where
  | Zero : Z2
  | One : Z2
  deriving Repr, BEq

def addZ2 (x y : Z2) :=
  if x == y then Z2.Zero else Z2.One
  -- As a Cayley table:
  --match x,y with
  --| Z2.Zero, Z2.Zero => Z2.Zero
  --| Z2.Zero, Z2.One  => Z2.One
  --| Z2.One,  Z2.Zero => Z2.One
  --| Z2.One,  Z2.One  => Z2.Zero


instance : Group Z2 where
  mul := addZ2
  one := Z2.Zero
  inv := id
  mul_assoc f g h := sorry
  one_mul := sorry
  mul_one := sorry
  mul_left_inv := sorry
