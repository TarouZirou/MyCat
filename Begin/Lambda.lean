import Mathlib.Tactic.Basic
import Mathlib.Tactic
import Mathlib.Logic.ExistsUnique
import Init.Classical

universe u

/-- 確定記述について-/
class Iota (α : Type u) where
  ι : (α → Prop) → α
  rEq : ∀a:α, ι (Eq a) = a

variable (α β γ : Type*)
variable (P Q R : Prop)
variable (A B C: α → Prop)

theorem T₁ (A : α) : A = A := rfl
theorem T₂ (A B : Prop) (hA : A) (hAB : A = B) : B := by
  rw [hAB] at hA
  assumption

theorem T₅ (f : α → β) : f = (λ x ↦ f x) := rfl
theorem T₇ (A : α) : True = (A = A) := Eq.symm (eq_self A)
theorem T₈ : (True ∧ True) = True := true_and True
theorem T₉ : True ∧ True := ⟨trivial, trivial⟩
theorem T₁₀ (A B : α) (C D : β) (hAB : A = B) (hCD : C = D) : (A = B) ∧ (C = D) := ⟨hAB, hCD⟩
theorem T₁₁ : (True ∧ False) = False := and_false True
theorem T₁₃ : (True ∧ P) = P := true_and P
theorem T₁₄ : (True = False) = False := Lean.Grind.eq_eq_of_eq_true_left rfl
theorem T₁₅ : (True = P) = P := Lean.Grind.eq_eq_of_eq_true_left rfl
theorem T₁₆ : P ↔ (True = P) := by
  refine Iff.symm (Eq.to_iff ?_)
  exact T₁₅ P

theorem T₁₉ : (True → P) = P := true_implies P
theorem T₂₀ (hP : P) (hPQ : P → Q) : Q := hPQ hP

theorem curry (f : α × β → γ) (g : α → β → γ) : g = (λ a b ↦ f ⟨a, b⟩) ↔ (∀ a b, f ⟨a, b⟩ = g a b) := by
  constructor
  intro h
  rw [h]
  intro a b
  rfl
  intro h
  funext a b
  symm
  exact h a b

--variable (ι : (α → Prop) → α)
--axiom A₅ (a : α): ι (Eq a) = a

theorem Tp₁ [Iota α] (y : α): (∀ z : α, (A z = (y = z))) → (Iota.ι A = y) := by
  intro h
  apply funext_iff.mpr at h
  rw [h]
  exact Iota.rEq y

theorem ex_uni_eq_lam [Iota α] : (∃! x : α, A x) ↔ (∃ y : α, A = (Eq y))  := by
  constructor
  rintro ⟨x, hAx, huniq⟩
  refine ⟨x, funext fun a => propext ⟨?_,?_⟩⟩
  intro hAa
  simp at huniq
  exact (huniq a hAa).symm
  intro xeqa
  rwa [xeqa] at hAx
  rintro ⟨y, heq⟩
  refine ⟨y, ?_, ?_⟩
  simp
  rw [heq]
  intro x
  simp
  rw [heq]
  exact Eq.symm

theorem Tp₂ [Iota α] : (∃! (x : α), A x) → A (Iota.ι A) := by
  intro hx
  apply (ex_uni_eq_lam α A).mp at hx
  rcases hx with ⟨a, hAa⟩
  rw [hAa]
  symm
  exact Iota.rEq a

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [zero_add]


def ω : Nat → Prop := 
  λ x ↦ (∀ z : Nat → Prop, (z 0 ∧ ∀ y : Nat, (z y → z (y + 1))) → z x)

def i [Iota α] : (α → Prop) → α := λ A ↦ Iota.ι A

#check α → Prop

def recu [Iota Nat] : (Nat → Nat → Nat) → (Nat → Nat → Nat) := 
  (λ h g k ↦ 
    i Nat (λ l : Nat ↦ 
      (∀ u : Nat → Nat → Prop,
        (u 0 g ∧ ∀ x y : Nat, (u x y → u (x + 1) (h x y))) → u k l
      )
    )
  )

/-- Todo: この定理はいつか証明する。-/
/-theorem Tpp₁ [Iota Nat] (h : Nat → Nat → Nat) (g : Nat): 
  ((recu h g) 0 = g) ∧
  ∀ z : Nat, ((recu h g) (z + 1) = h z ((recu h g) z)) := by
  rw [recu, i]
  constructor
  induction g with
    | zero => 
      sorry
    | succ n => sorry
  sorry
-/

example : (P → Q → R) → (P → Q) → P → R := λ pqr pq p ↦ pqr p (pq p)