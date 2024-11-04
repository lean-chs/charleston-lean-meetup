namespace notes20241112

----------------
-- Structures --
----------------

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

example := Point.mk 1.5 2.8

#check Point.mk
#check Point.x

-- Can name the constructor with:
structure Point2 where
  bippity_boppity_point ::
  x : Float
  y : Float
deriving Repr

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

-- Can put type annotation inside curly braces
#check { x := 0.0, y := 0.0 : Point}

def zeroX (p : Point) : Point :=
  { p with x := 0 }

-- inheritance
structure Point3d extends Point where
  z : Float
deriving Repr

#check Point3d.mk
#check { x := 0.0, y := 0.0, z := 0.0 : Point3d}

---------------------------
-- Accessor dot notation --
---------------------------

-- More generally, accessor notation has the form TARGET.f ARG1 ARG2 ....
-- If TARGET has type T, the function named T.f is called.
-- TARGET becomes its leftmost argument of type T, which is often but not always the first one,
-- and ARG1 ARG2 ... are provided in order as the remaining arguments.

inductive Foo where
  | foo : Foo
  | bar : Foo
deriving Repr

def Foo.baz (f : Foo) : Nat :=
  match f with
  | foo => 0
  | bar => 1

#check Foo.foo.baz
#check "hey".append " there"


------------------
-- Polymorphism --
------------------

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def swap {α : Type} (point : PPoint α) : PPoint α :=
  { x := point.y, y := point.x }

-----------
-- Lists --
-----------

def xs : List Nat := [2, 3, 5, 7]

def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | []      => 0
  | y :: ys => Nat.succ (length α ys)

------------
-- Option --
------------

def head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | []     => none
  | y :: _ => some y

def getWithDef {α : Type} (ma : Option α) (d : α) : α :=
  match ma with
  | none   => d
  | some a => a


----------------------
-- Products / Pairs --
----------------------

def fives : String × Int := ("five", 5)

-------------------
-- Let bindings  --
-------------------

example (m n : Nat) : Nat :=
  let z := m + 2
  z + n

--------------------------------
-- flexible pattern matching  --
--------------------------------

example (m n : Nat) : Nat :=
  match m, n with
  | 0, 0 => 0
  | _, x+1  => x
  | _, _  => 2

-------------
-- if let  --
-------------

example (xs : List Nat) : Nat :=
  if let some x := head? xs then
    x
  else 0

--------------------------
-- String Interpolation --
--------------------------

#eval s!"one plus one is {1 + 1}"

--
-- Type Classes
--

class Plus (α : Type) where
  plus : α → α → α

open Plus (plus)

instance : Plus Nat where
  plus := Nat.add

instance : Plus Foo where
  plus x y :=
    match x, y with
    | Foo.foo, z => z
    | Foo.bar, Foo.foo => Foo.bar
    | Foo.bar, Foo.bar => Foo.foo

#eval plus 3 4
#eval plus Foo.foo Foo.bar

instance [Plus α] : Plus (PPoint α) where
  plus p1 p2 := { x := plus p1.x p2.x, y := plus p1.y p2.y }

def plus_self [Plus α] (x : α) : α :=
  plus x x

--
-- Monads
--

example (xs : List Nat) : Option Nat := do
  let x ← head? xs
  pure (x + 1)

--
-- Coercions
--

instance : Coe Foo Nat where
  coe x :=
    match x with
    | Foo.foo => 0
    | Foo.bar => 1

#eval (Foo.foo : Nat)

end notes20241112
