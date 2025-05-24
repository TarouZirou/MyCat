import Init.Classical
import Mathlib.CategoryTheory.EpiMono

variable (P Q R : Prop)

example : P ∧ Q → P := λ ⟨p, _⟩ ↦ p
example : P ∧ Q → Q := λ ⟨_, q⟩ ↦ q
example : P → P ∨ Q := λ p ↦ Or.inl p
example : Q → P ∨ Q := λ q ↦ Or.inr q
example : P → Q → P := λ p _ ↦ p
example : (P → Q) → P → Q := λ pq p ↦ pq p
example : (P → Q) → (Q → R) → (P → R) := λ pq qr p ↦ (qr ∘ pq) p
example : (P → Q) → (¬Q → ¬P) := λ pq nq p ↦ (nq ∘ pq) p
example : ((P ∧ Q) → R) → (P → Q → R) := λ pqrr p q ↦ pqrr ⟨p, q⟩
example : (P → Q → R) → ((P ∧ Q) → R) := λ pqr ⟨p, q⟩ ↦ pqr p q
example : (P → Q → R) ↔ ((P ∧ Q) → R) :=
  Iff.intro
    (λ pqr ⟨p, q⟩ ↦ pqr p q)
    (λ pqrr p q ↦ pqrr ⟨p, q⟩)
