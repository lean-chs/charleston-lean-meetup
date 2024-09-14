namespace notes20241008

variable {α : Type}
variable {β : α → Type}

variable {p : α → Prop}

#check ∀ x, p x
#check (x : α) → p x

#check ∀ a : α, β a
------ Π x : α, β x
#check (x : α) → β x

#check (∃ x, p x)
#check Exists λ (x:α) => p x

#check Exists.intro
#check Exists.intro 3 (rfl : 3 = 3)
#check Exists.elim


example (h : ∃ x, p x) : ∃ x, p x ∧ p x :=
  match h with
  | Exists.intro w hw => Exists.intro w (And.intro hw hw)

example (h : ∃ x, p x) : ∃ x, p x ∧ p x :=
  let ⟨w, hw⟩ := h; ⟨w, hw, hw⟩


-- Proof irrelevance forbids:
--example (h : ∃ x, p x) : α :=
--  match h with
--  | Exists.intro w hw => w

def proof_irrelevance (q : Prop) (proof_1 proof_2 : q) : proof_1 = proof_2 := rfl

-- Exists.intro a h has type (∃ x : α, p x) : Prop
-- Sigma.mk a h     has type (Σ x : α, p x) : Type
--
-- https://github.com/leanprover/lean4/blob/f989520d2b17ec2fe987a69fee44a5272be1ff10/src/Init/Core.lean#L255

#check ∃ x : α, p x
#check Σ x : α, β x

example (h : Σ x, β x) : α :=
  match h with
  | Sigma.mk a _ba => a


def WeakExists (q : α → Prop) := ¬ ∀ x, ¬ q x

example (h : ∃ x, p x) : WeakExists p :=
  Exists.elim h (λ a pa hnp => hnp a pa)


namespace barber_paradox

variable (person : Type) (barber : person)
variable (shaves : person → person → Prop)

example (h : ∀ x : person, shaves barber x ↔ ¬ shaves x x) : False :=
  sorry

end barber_paradox

example (a : α) : (∃ x, p x → r) → (∀ x, p x) → r := sorry

example : ¬ (∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

example : (∃ x, ¬ p x) → ¬ (∀ x, p x) := sorry


variable {A B : Type}
variable {R : A → B → Type}

--example : (Π x : A, → Σ y : B, R x y) → Σ f : (A → B), Π x : A, → R x (f x) :=
example : ((a : A) → Σ b : B, R a b) → Σ f : (A → B), ((a : A) → R a (f a)) :=
  λ h => ⟨λ x => (h x).fst, λ x => (h x).snd⟩

end notes20241008
