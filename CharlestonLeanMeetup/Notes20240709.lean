namespace notes20240709

/-

== Inductive Types ==

inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo

-/


-- Example: Lists

inductive L (α : Sort u) where
  | nil : L α
  | cons : α → L α → L α

example : L Nat := L.cons 17 (L.cons 42 L.nil)


def length (xs : L α) : Nat :=
  match xs with
  | L.nil => sorry
  | L.cons _ xs => sorry






-- Example: Optional / Maybe

inductive Opt α where
  | nothing : Opt α
  | just : α → Opt α


def head : L α → Opt α
  | L.nil => Opt.nothing
  | L.cons x _ => Opt.just x



-- Example: Natural Numbers 0, 1, 2, …

inductive N where
  | zero : N
  | succ : N → N
  deriving Repr -- for #eval


def one := N.succ N.zero
def two := N.succ one
def three := N.succ two


def addN (m n : N) : N :=
  match n with
  | N.zero   => m
  | N.succ n => N.succ (addN m n)


#eval addN one two
example : addN one two = three := rfl


-- The Add typeclass lets us use the plus symbol
instance : Add N where
  add := addN


/-

GOALS for N:

1) (x + y) + z = x + (y + z)

2) x + y = y + x

3) m + n = p + n → m = p

Tools:

1) rfl
2) structural recursion
3) rewriting (rw tactic)
4) congrArg: IF a = b THEN f(a) = f(b)

-/


-- Two easy theorems:

theorem add_zero (m : N) : m + N.zero = m := sorry

-- Notice this fails to work:
--theorem zero_add (m : N) : N.zero + m = m := rfl

#print add_zero


theorem add_succ (m n : N) : m + (N.succ n) = N.succ (m + n) := sorry



-- DETOUR: the magic of RFL
-- Note we haven't seen Indexed Families yet

inductive IsTheSameAs {α : Sort u} (a : α) : α → Prop where
  | funnel_of_truth : IsTheSameAs a a

theorem one_and_one_is_two : IsTheSameAs (one + one) two := IsTheSameAs.funnel_of_truth

infix:50 " 🍕 " => IsTheSameAs
theorem one_and_one_is_still_two : one + one 🍕 two := IsTheSameAs.funnel_of_truth



-- Back to arithmetic!


theorem succ_add (m n : N) : N.succ m + n = N.succ (m + n) :=
  match n with
  | N.zero => sorry
  | N.succ x => sorry

#print congrArg



theorem zero_add (n : N) : N.zero + n = n :=
  match n with
  | N.zero => sorry
  | N.succ x => sorry

#print zero_add


theorem add_comm (m n : N) : m + n = n + m :=
  match n with
  | N.zero => sorry
  | N.succ x => sorry


theorem add_assoc (m n p : N) : m + (n + p) = (m + n) + p :=
  match p with
  | N.zero => sorry
  | N.succ q => -- show  m + (n + (q+1)) = (m + n) + (q + 1)
      sorry


def pred (m : N) : N :=
  match m with
  | N.zero => N.zero
  | N.succ n => n

theorem succ_inj {m n : N} (h : N.succ m = N.succ n) : m = n :=
  sorry

theorem add_cancel_right {m n p : N} (h : m + n = p + n) : m = p :=
  match m with
  | N.zero => sorry
  | N.succ m' => sorry

theorem add_cancel_left {m n p : N} (h : m + n = m + p) : n = p :=
  sorry


/-

🎉 GOALS COMPLETE 🎉

What could we do next?

* Multiplication
* Arithmetic facts
* Binary notation
* Integers

-/


-- Multiplication

def mult (m n : N) : N :=
  match n with
  | N.zero   => N.zero
  | N.succ n => (mult m n) + m

instance : Mul N where
  mul := mult

theorem mult_assoc (m n p : N) : (m * n) * p = m * (n * p) := sorry
theorem mult_comm (m n : N) : m * n = n * m := sorry
theorem mult_distr_add (m n p: N) : m * (n + p) = (m * n) + (m * p) := sorry




-- Binary representation of numbers

inductive Bin where
  | ε : Bin
  | O : Bin → Bin
  | I : Bin → Bin


open Bin

notation:50 x "◯" => Bin.O x
notation:50 x "Ⅰ" => Bin.I x


def eight := ε Ⅰ ◯ ◯ ◯



def incr (b : Bin) : Bin :=
  match b with
  | ε   => ε Ⅰ
  | ε Ⅰ => ε Ⅰ ◯
  | b ◯ => b Ⅰ
  | b Ⅰ => (incr b) ◯

def toN (b : Bin) : N :=
  match b with
  | ε     => N.zero
  | b' ◯ => toN b' + toN b'
  | b' Ⅰ  => toN b' + toN b' + N.succ N.zero

def toB (n : N) : Bin :=
  match n with
  | N.zero => ε ◯
  | N.succ n => incr (toB n)

-- Prove if true, find counterexample otherwise

theorem incr_succ (b : Bin) : toN (incr b) = N.succ (toN b) := sorry

theorem to_from (b : Bin) : toB (toN b) = b := sorry

theorem from_to (n : N) : toN (toB n) = n := sorry




-- Integers
--
-- we represent x ∈ ℤ by (x, y)
-- where (x, y) is thought of as x - y

inductive Z where
  | mk : N → N → Z

-- (a - b) = (c - d) IFF a + d = c + b
def Zequiv (x y : Z) : Prop :=
  match (x, y) with
  | (Z.mk a b, Z.mk c d) => a + d = c + b

infix:50 " ~ " => Zequiv

-- Zequiv is an Equivalenc Relation
--
-- Reflexive:  x ~ x
-- Symetric:   IF x ~ y THEN y ~ x
-- Transitive: IF x ~ y AND y ~ z THEN x ~ z

theorem ze_refl (x : Z) : x ~ x := rfl

theorem ze_symm : ∀ {x y : Z}, x ~ y → y ~ x := sorry

theorem add_eqns : ∀ {a b c d : N}, a = b → c = d → a + c = b + d :=
  sorry

theorem ze_trans : ∀ {x y z : Z}, x ~ y → y ~ z → x ~ z :=
  sorry


theorem ze_equivalence : Equivalence Zequiv :=
  { refl := ze_refl, symm := ze_symm, trans := ze_trans }

instance : Setoid Z where
  r     := Zequiv
  iseqv := ze_equivalence

def neg_two := Quotient.mk' (Z.mk N.zero two)
#check neg_two

end notes20240709
