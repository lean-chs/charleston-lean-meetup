namespace notes20240813

-- Fixed lengh vectors

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

def vtos [ToString α] (vs : Vect α n) : String :=
  match vs with
    | Vect.nil             => "]"
    | Vect.cons x Vect.nil => s!"{x}]"
    | Vect.cons x xs       => s!"{x}, {vtos xs}"

instance [ToString α] : ToString (Vect α n) where
  toString xs := s!"[{vtos xs}"

def list₁ : Vect Nat 2 := Vect.cons 2 (Vect.cons 1 (Vect.nil))
def list₂ : Vect Nat 1 := .cons 1 .nil
def list₃ : Vect String 1 := .cons "a" .nil

#eval toString list₁
#eval toString list₂
#eval toString list₃

--example : Vect String 3 := Vect.nil

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

#eval toString (Vect.replicate 3 "a")

def Vect.head : Vect α (n+1) → α
  | .cons x _ => x

#eval Vect.head list₁

--def Vect.head' : Vect Nat (n) → Nat
--  | .cons x _ => x


def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

--#check Vect.zip list₁ list₂
#eval Vect.zip list₂ list₃

theorem zero_add {n : Nat} : n = 0 + n :=
  match @n with
  | 0 => rfl
  | _ + 1 => congrArg (· + 1) zero_add

theorem succ_add {m n : Nat} : (m + 1) + n = (m + n) + 1 :=
  match @n with
  | 0 => rfl
  | k + 1 =>
    have h : ((m + 1) + k) + 1 = (m + (k + 1)) + 1 :=
      congrArg (· + 1) succ_add
    h

def appendL {n k : Nat} : Vect α n → Vect α k → Vect α (n + k)
  | xs, Vect.nil => xs
  | xs, .cons y ys => .cons y (appendL xs ys)

def appendR {n k : Nat} : Vect α n → Vect α k → Vect α (n + k)
  | Vect.nil, ys => zero_add ▸ ys
  | .cons x xs, ys => succ_add ▸ .cons x (appendR xs ys)

#eval toString (appendR (.cons 1 (.cons 2 .nil)) (.cons 3 (.cons 4 .nil)))
#eval toString (appendL (.cons 1 (.cons 2 .nil)) (.cons 3 (.cons 4 .nil)))


def list_to_vector (xs : List α) : Vect α (List.length xs) :=
  match xs with
  | [] => Vect.nil
  | y::ys => Vect.cons y (list_to_vector ys)


-- safe indexing Arrays

def arr : Array Nat := #[1, 2, 3]

#eval arr[0]
#eval arr.push 4
--#eval arr[5]



def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i


def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0


def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by arr.size - i

def Array.find (arr : Array α) (p : α → Bool) : Option (Nat × α) :=
  findHelper arr p 0
