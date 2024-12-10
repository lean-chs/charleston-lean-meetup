import Std
open Std (HashMap)

--------
-- 1A --
--------

def f1a (s : String) : Nat × Nat :=
  let x := String.splitOn s "   "
  (String.toNat! x[0]!, String.toNat! x[1]!)

def dist (p : Nat × Nat) : Nat :=
  if p.fst > p.snd then p.fst - p.snd else p.snd - p.fst

def day_1_a (lines : List String) : Nat :=
  let xs := List.map f1a lines
  let as := (List.map Prod.fst xs).mergeSort
  let bs := (List.map Prod.snd xs).mergeSort
  let zs := List.zip as bs
  List.sum $ List.map dist zs


def counts (xs : List Nat) : HashMap Nat Nat :=
  let bump := λ
              | .none => .some 1
              | .some c => .some (c+1)
  List.foldl (λ a b => HashMap.alter a b bump) HashMap.empty xs
-- on Zulip, James Sully did this lovely impl:
-- ns.foldl (init := ∅) λ map n ↦ map.alter n λ
-- | .none => .some 1
-- | .some count => .some <| count + 1


--------
-- 1B --
--------

def day_1_b (lines : List String) : Nat :=
  let xs := List.map f1a lines
  let as := (List.map Prod.fst xs).mergeSort
  let bs := (List.map Prod.snd xs).mergeSort
  let cs := counts bs
  let zs := List.map (λ n => n * HashMap.getD cs n 0) as
  List.sum zs


--------
-- 2A --
--------

def toNats (s : String) : List Nat :=
  List.map String.toNat! (String.splitOn s " ")


def step_2a (a : Option (Ordering × Nat)) (n : Nat) :
  Option (Ordering × Nat) :=
  let not_too_far := λ (x y z : Nat) (o : Ordering) =>
      if x - y <= 3 then some (o, z) else none
  match a with
  | none => none
  | some (o, m) =>
      match (o, compare m n) with
      | (_, .eq) => none
      | (.eq, .lt) => not_too_far n m n .lt
      | (.eq, .gt) => not_too_far m n n .gt
      | (.lt, .lt) => not_too_far n m n .lt
      | (.gt, .gt) => not_too_far m n n .gt
      | _ => none

def f2a (ns : List Nat) : Option (Ordering × Nat) :=
  if let (m::ms) := ns
    then List.foldl step_2a (some (.eq, m)) ms
    else none

def day_2_a (lines : List String) : Nat :=
  let xs := List.map toNats lines
  let ys := List.filterMap f2a xs
  ys.length


def remove_i (xs : List Nat) (i : Nat) : List Nat :=
  (List.take i xs) ++ (List.drop (i+1) xs)


--------
-- 2B --
--------

def f2b (ns : List Nat) : Option (Ordering × Nat) :=
  let f := λ acc i =>
    match acc with
    | some x => some x
    | none =>
        match remove_i ns i with
        | [] => none
        | m::ms => List.foldl step_2a (some (.eq, m)) ms

  List.foldl f none (List.range $ List.length ns)


def day_2_b (lines : List String) : Nat :=
  let xs := List.map toNats lines
  let ys := List.filterMap f2b xs
  ys.length

--------
-- 3A --
--------

structure State3 where
  good : Char
  num1 : Option (List Char)
  num2 : Option (List Char)
  completed : List Nat

instance : ToString State3 where
  toString s := s!"{s.good} - {s.num1} - {s.num2} - {s.completed}"

def emptyS3 : State3 := State3.mk ' ' none none []

def mult (ns ms : List Char) : Nat :=
  let n := String.mk ns
  let m := String.mk ms
  n.toNat! * m.toNat!

def step3a (st : State3) (c : Char) : State3 :=
  match (st, c) with
  | (⟨' ', none, none, _⟩ , 'm')
    => {st with good := 'm'}
  | (⟨'m', none, none, _⟩ , 'u')
    => {st with good := 'u'}
  | (⟨'u', none, none, _⟩ , 'l')
    => {st with good := 'l'}
  | (⟨'l', none, none, _⟩ , '(')
    => {st with good := '('}
  | (⟨'(', none, none, comp⟩ , x)
    => if x.isDigit
       then {st with good := '1', num1 := some [x]}
       else {emptyS3 with completed := comp}
  | (⟨'1', some ds, none, comp⟩ , x)
    => if x.isDigit
       then {st with num1 := some (ds ++ [x])}
       else if x == ','
            then {st with good := ','}
            else {emptyS3 with completed := comp}
  | (⟨',', _, _, comp⟩ , x)
    => if x.isDigit
       then {st with good := '2', num2 := some [x]}
       else {emptyS3 with completed := comp}
  | (⟨'2', some ns, some ms, comp⟩ , x)
    => if x.isDigit
       then {st with num2 := some (ms ++ [x])}
       else if x == ')'
            then {emptyS3 with completed := (mult ns ms)::comp}
            else {emptyS3 with completed := comp}
  | (⟨_, _, _, comp⟩ , _)
    => {emptyS3 with completed := comp}

def f3a (s : String) : State3 :=
  let cs := s.toList
  List.foldl step3a emptyS3 cs

def day_3_a (lines : List String) : Nat :=
  let xs := List.map f3a lines
  let ys := List.map (λ x => x.completed) xs
  let zs := List.map List.sum ys
  List.sum zs


--------
-- 3B --
--------

structure State3b where
  good : Char
  num1 : Option (List Char)
  num2 : Option (List Char)
  completed : List Nat
  on : Bool

instance : ToString State3b where
  toString s :=
    s!"{s.good} - {s.num1} - {s.num2} - {s.completed} - {s.on}"

def emptyS3b : State3b := State3b.mk ' ' none none [] true

def step3b (st : State3b) (c : Char) : State3b :=
  match (st, c) with
  | (⟨_, none, none, _, _⟩ , 'm')
    => {st with good := 'm'}
  | (⟨'m', none, none, _, _⟩ , 'u')
    => {st with good := 'u'}
  | (⟨'u', none, none, _, _⟩ , 'l')
    => {st with good := 'l'}
  | (⟨'l', none, none, _, _⟩ , '(')
    => {st with good := '('}
  | (⟨'(', none, none, comp, o⟩ , x)
    => if x.isDigit
       then {st with good := '1', num1 := some [x]}
       else {emptyS3b with completed := comp, on := o}
  | (⟨'1', some ds, none, comp, o⟩ , x)
    => if x.isDigit
       then {st with num1 := some (ds ++ [x])}
       else if x == ','
            then {st with good := ','}
            else {emptyS3b with completed := comp, on := o}
  | (⟨',', _, _, comp, o⟩ , x)
    => if x.isDigit
       then {st with good := '2', num2 := some [x]}
       else {emptyS3b with completed := comp, on := o}
  | (⟨'2', some ns, some ms, comp, o⟩ , x)
    => if x.isDigit
       then {st with num2 := some (ms ++ [x])}
       else if x == ')'
            then
              if st.on
              then {emptyS3b with completed := (mult ns ms)::comp, on := o}
              else {emptyS3b with completed := comp, on := o}
            else {emptyS3b with completed := comp, on := o}

  | (⟨_, _, _, comp, o⟩ , 'd')
    => {emptyS3b with good := 'd', completed := comp, on := o}
  | (⟨'d', _, _, _, _⟩ , 'o')
    => {st with good := 'o'}
  | (⟨'o', _, _, _, _⟩ , '(')
    => {st with good := '{'}
  | (⟨'{', _, _, comp, _⟩ , ')')
    => {emptyS3b with completed := comp, on := true}

  | (⟨'o', _, _, _, _⟩ , 'n')
    => {st with good := 'n'}
  | (⟨'n', _, _, _, _⟩ , '\'')
    => {st with good := '\''}
  | (⟨'\'', _, _, _, _⟩ , 't')
    => {st with good := 't'}
  | (⟨'t', _, _, _, _⟩ , '(')
    => {st with good := '['}
  | (⟨'[', _, _, comp, _⟩ , ')')
    => {emptyS3b with completed := comp, on := false}

  | (⟨_, _, _, comp, o⟩ , _)
    => {emptyS3b with completed := comp, on := o}


def f3b (s : String) : State3b :=
  let cs := s.toList
  List.foldl step3b emptyS3b cs


def day_3_b (lines : List String) : Nat :=
  let cs := List.flatten (List.map String.toList lines)
  let rs := List.foldl step3b emptyS3b cs
  List.sum rs.completed

--------
-- 4A --
--------

structure Grid where
  tiles : List (List Char)
  len : Nat

def mk_grid (ts : List (List Char)) : Grid :=
  Grid.mk ts (ts.length)

def grid (g : Grid) (x y : Nat) : Char := g.tiles[y]![x]!

def Quad := Char × Char × Char × Char
deriving BEq

def MQuad := Option Quad

def get_possible!
  (g : Grid) (x0 y0 : Nat) (fx fy : Nat → Nat) : Quad :=
    let (x1, y1) := (fx x0, fy y0)
    let (x2, y2) := (fx x1, fy y1)
    let (x3, y3) := (fx x2, fy y2)
    ( grid g x0 y0 , grid g x1 y1 , grid g x2 y2 , grid g x3 y3)

def make_direction
  (fx fy : Nat → Nat)
  (p : Nat → Nat → Bool)
  (g : Grid)
  (x0 y0 : Nat)
  : MQuad :=
  if p x0 y0
    then some $ get_possible! g x0 y0 fx fy
    else none

def can_up (_ y : Nat) : Bool := y > 2
def can_dn (l _ y : Nat) : Bool := y + 3 < l
def can_lf (x _ : Nat) : Bool := x > 2
def can_rt (l x _ : Nat) : Bool := x + 3 < l

def can_both
  (f g : Nat → Nat → Bool) (x y : Nat) : Bool := f x y && g x y

def up : Grid → Nat → Nat → MQuad :=
  make_direction id (· - 1) can_up

def dn (g : Grid) : Nat → Nat → MQuad :=
  make_direction id (· + 1) (can_dn g.len) g

def lf : Grid → Nat → Nat → MQuad :=
  make_direction (· - 1) id can_lf

def rt (g : Grid) : Nat → Nat → MQuad :=
  make_direction (· + 1) id (can_rt g.len) g

def ul : Grid → Nat → Nat → MQuad :=
  make_direction (· - 1) (· - 1) (can_both can_up can_lf)

def ur (g : Grid) : Nat → Nat → MQuad :=
  make_direction (· + 1) (· - 1) (can_both can_up (can_rt g.len)) g

def dl (g : Grid) : Nat → Nat → MQuad :=
  make_direction (· - 1) (· + 1) (can_both (can_dn g.len) can_lf) g

def dr (g : Grid) : Nat → Nat → MQuad :=
  make_direction (· + 1) (· + 1) (can_both (can_dn g.len) (can_rt g.len)) g

def xmas (v : MQuad) : Option Unit :=
  match v with
  | none => none
  | some w => if w == ('X', 'M', 'A', 'S') then some () else none

def tile_options (x y : Nat) (g : Grid) : Nat :=
  let options := [up, dn, lf, rt, ul, ur, dl, dr]
  let ds := List.map (λ f => f g x y) options
  List.length $ List.filterMap xmas ds

def day_4_a (lines : List String) : Nat :=
  let g := mk_grid (List.map String.toList lines)
  let ns := (List.range $ g.len * g.len)
  let ps := List.map (λ n => (n / g.len, n % g.len)) ns
  List.foldl (λ acc (x, y) => acc + tile_options x y g) 0 ps

--------
-- 4B --
--------

def x_mas (x y : Nat) (g : Grid) : Bool :=
  let a := grid g x y == 'A'
  let ul := grid g (x-1) (y-1)
  let ur := grid g (x+1) (y-1)
  let dl := grid g (x-1) (y+1)
  let dr := grid g (x+1) (y+1)

  let ms := match (ul, ur) with
            | ('M', 'M') => dl == 'S' && dr == 'S'
            | ('M', 'S') => dl == 'M' && dr == 'S'
            | ('S', 'M') => dl == 'S' && dr == 'M'
            | ('S', 'S') => dl == 'M' && dr == 'M'
            | _ => false
  a && ms

def day_4_b (lines : List String) : Nat :=
  let g := mk_grid (List.map String.toList lines)
  let l := g.len - 2
  let ns := (List.range $ l * l)
  let ps := List.map (λ n => ((n / l) + 1, (n % l) + 1)) ns
  List.foldl
    (λ acc (x, y) => if x_mas x y g then acc + 1 else acc)
    0
    ps


def main (args : List String) : IO UInt32 :=
  match args with
  | [] => do
      IO.println "pass a filename"
      pure 1
  | filename::_ => do
      let ans <- (day_4_b ∘ Array.toList) <$> IO.FS.lines ⟨filename⟩
      IO.println ans
      pure 0
