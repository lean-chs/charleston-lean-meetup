namespace notes20240114

-- https://wiki.haskell.org/index.php?title=Monad_laws
--
-- a type (M α) is a *Monad* if it has functions:
--   * pure : α → M α
--   * bind : M α → (α → M β) → M β
--
-- such that 3 properties hold
--   * left identity
--   * right identity
--   * associativity
--
--- The statement:
--      bind ma f
--  can be written:
--      ma >>= f
--
--  Moreover, there is "do notation"
--
--  do
--    x <- action1
--    y <- action2
--    action3 x y
--
--  desugars as
--
--  action1 >>= (λ x => ... )
--
--  action1 >>= (λ x => action2 >>= (λ y => ... ))
--
--  action1 >>= (λ x => action2 >>= (λ y => action3 x y))
--
-- Back to the 3 properties.
--
-- == left identity ==
--
--   pure a >>= f = f a
--
--   do                      do
--     x <- pure x    =        f x
--     f x
--
-- == right identity ==
--
--   m >>= pure = m
--
--   do                 do
--     x <- m    =        m
--     pure x
--
-- == associativity ==
--
-- (m  >>= f) >>= g = m >>= (λ a => (f a) >>= g)
--
--  do              do                do
--    y <- do         x <- m            x <- m
--      x <- m   =    do           =    y <- f x
--      f x             y <- f x        g y
--    g y               g y
--
--
-- The Fish
-- (Kleisli-composition operator)
--
--   >=>
--
--  f >=> g  =  λ x => f x >>= g
--
--   * left identity   - pure >=> f = f
--   * right identity  - f >=> pure = f
--   * associativity   - (f >=> g >=>) >=> h = f >=> (g >=> h)
--
-- Note that these are the axioms for a category!

-- ===========
-- == Maybe ==
-- ===========

inductive Maybe α where
  | none : Maybe α
  | just : α → Maybe α


instance : Monad Maybe where
  pure a := .just a
  bind ma f :=
    match ma with
    | .none => .none
    | .just x => f x

example : Maybe Nat :=
  do
    let x <- .just 4
    let y <- .just 5
    return (x+y)


def left_identity_maybe (a : α) (f : α → Maybe β) :

  pure a >>= f = f a

  := rfl


def right_identity_maybe (ma : Maybe α) :

  ma >>= pure = ma

  :=
  match ma with
  | .none => rfl
  | .just _ => rfl


def assoc_maybe (ma : Maybe α) (f : α → Maybe β)  (g : β → Maybe γ):

  (ma  >>= f) >>= g = ma >>= (λ c => (f c) >>= g)

  :=
  match ma with
  | .none => rfl
  | .just _ => rfl


-- ============
-- == Writer ==
-- ============

inductive Writer Λ α where
  | writer : Λ → α → Writer Λ α

class Monoid (α : Type) where
  e : α
  opp : α → α → α
  left_id : α → opp e a = a

instance [Monoid Λ] : Monad (Writer Λ) where

  pure a := .writer Monoid.e a

  bind ma f :=
    match ma with
    | .writer l a =>
        match f a with
        | .writer l' b' => .writer (Monoid.opp l l') b'

-- helpers for left identity proof
def get_l (w : Writer Λ α) : Λ := match w with | .writer l _ => l
def get_a (w : Writer Λ α) : α := match w with | .writer _ a => a

def unpack_pure (a : α) [Monoid Λ] (f : α → Writer Λ β) :
  (Writer.writer Monoid.e a) >>= f
    = .writer (Monoid.opp Monoid.e (get_l $ f a)) (get_a $ f a) :=
  rfl
-- end

def left_identity_wr (Λ α β : Type) [Monoid Λ] (a : α) (f : α → Writer Λ β) :
  (pure a) >>= f = f a :=
  match h : f a with
  | .writer l b =>
    have h0 : (pure a : Writer Λ α) = (Writer.writer Monoid.e a) := rfl
    have h1: get_l (f a) = l := by rw [h]; rfl
    have h2: get_a (f a) = b := by rw [h]; rfl
    by rw [h0, unpack_pure a f, h1, h2, Monoid.left_id l]


def right_identity_wr (α : Type) (ma : Maybe α) : ma >>= .just = ma :=
  match ma with
  | .none => rfl
  | .just _ => rfl


def assoc_wr (α : Type) (ma : Maybe α) (f : α → Maybe β)  (g : β → Maybe γ):
  (ma  >>= f) >>= g = ma >>= (λ c => (f c) >>= g) :=
  match ma with
  | .none => rfl
  | .just _ => rfl


-- ============
-- == Reader ==
-- ============

inductive Reader ρ α where
  | reader : (ρ → α) → Reader ρ α

instance (ρ : Type) : Monad (Reader ρ) where

  pure a := .reader (λ _ => a)

  bind ma f :=
    match ma with
    | .reader g =>
        .reader (λ r => match f (g r) with | .reader h => h r)


-- ==========
-- == List ==
-- ==========

instance : Monad List where

  pure x := [x]

  bind xs f := List.flatMap xs f


def list_comp_ex : List Nat :=
  do
    let x <- List.range 3
    pure (x+1)

#eval list_comp_ex

-- haskell:
--   [x+1 | x <- List.range 3]
--
-- python:
--   [x+1 for x in range(3)]

def list_comp_ex_2 : List (Nat × Char) :=
  do
    let x <- List.range 3
    let y <- ['a', 'b', 'c']
    pure (x, y)

#eval list_comp_ex_2

-- [(x, y) | x <- List.range 3, y <- ['a', 'b', 'c']]


-- ==============
-- == Identity ==
-- ==============

inductive Identity α where
  | wrap : α → Identity α

def unwrap (m : Identity α) : α := match m with | .wrap a => a

instance : Monad Identity where

  pure := .wrap

  bind a f := f (unwrap a)

-- ============
-- == Either ==
-- ============

inductive Either α β where
  | left : α → Either α β
  | right : β → Either α β

instance (α : Type) : Monad (Either α) where

  pure := .right

  bind a f :=
    match a with
    | .left error => .left error
    | .right val => f val

-- ===========
-- == State ==
-- ===========

inductive State σ α where
  | run : (σ → α × σ) → State σ α

instance (σ : Type) : Monad (State σ) where

  pure a := .run (λ s => (a, s))

  bind ma f := .run
    λ s =>
      match ma with
      | .run g =>
          let (a, s') := g s
          let .run h := f a
          h s'

def pop : State (List Nat) Nat :=
  .run $ λ | x::xs => (x,xs)
           | [] => (0, [])

def push (x : Nat) : State (List Nat) Unit :=
  .run $ λ | xs => ((),x::xs)

def poppin : State (List Nat) Unit := do
  let n <- pop
  let m <- pop
  push (n + m)

def run_state (s : State σ α) (s₀ : σ) : α × σ :=
  match s with | .run f => f s₀

#eval run_state poppin [1, 2, 3]


-- ========================
-- == Continuation (CPS) ==
-- ========================

inductive Cont r α where
  | run : ((α → r) → r) → Cont r α

def run_cont (c : Cont r α) : (α → r) → r :=
  match c with | .run f => f

instance (r : Type) : Monad (Cont r) where

  pure a := .run (λ f => f a)

  bind m f := .run $
    λ c => (run_cont m) λ a => run_cont (f a) c

-- https://wiki.haskell.org/MonadCont_under_the_hood

def f_cont (n : Nat) : Cont r Nat :=
  .run (λ c => c (n * 3))

def g_cont {r : Type} (n : Nat) : Cont r Nat :=
  do
    let x <- f_cont n
    let y <- pure (n - 2)
    pure (x + y)

def callback (x : Nat) : String := s!"you got {x}"

#eval run_cont (g_cont 5) callback

end notes20240114
