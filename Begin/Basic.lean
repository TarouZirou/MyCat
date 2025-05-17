import Mathlib.Tactic

def hello := "world"

variable (P Q R: Prop)
#check P

example : (P → Q) → P → Q:=
  λ f x ↦ f x

theorem pqp (P Q : Prop) : P → Q → P := by
  intro hp _
  exact hp

theorem pqplam (P Q : Prop) : P → Q → P := by
  have x : P → Q → P :=
    λ
      p -- p : P
      q ↦ -- q : Q
        p -- p : P
  exact x

theorem curry_howard (P Q R : Prop) : (P ∧ Q → R) ↔ (P → Q → R) := by
  have x : (P ∧ Q → R) → (P → Q → R) :=
    λ
      h -- P ∧ Q → R
      p -- p : P
      q ↦ -- q : Q
        -- このλは、A → (B → (C → D))という形を取っていて、
        -- h : A = P ∧ Q → R
        -- p : B = P
        -- q : C = Q
        -- h ⟨p, q⟩ : D = R
        -- の形となっている。
        h ⟨p, q⟩ -- ⟨p, q⟩ : P ∧ Q ↦ h ⟨p, q⟩ : R
  have y : (P → Q → R) → (P ∧ Q → R) :=
    λ
      h
      ⟨p, q⟩ ↦ -- ⟨p, q⟩ : P ∧ Q
        h p q -- p : P ↦ h p : Q ↦ h p q : R
  exact Iff.intro x y

theorem pqrqqpr (P Q R : Prop) : (P ∧ Q ↔ R ∧ Q) ↔ (Q → (P ↔ R)) := by
  have x : (P ∧ Q ↔ R ∧ Q) → (Q → (P ↔ R)) :=
    λ
      h -- h : (P ∧ Q ↔ R ∧ Q)
      q ↦ -- q : q
        Iff.intro
          -- p : P
          -- ⟨p, q⟩ : P ∧ Q
          -- h.1 : P ∧ Q → R ∧ Q
          -- h.1 ⟨p, q⟩ : R ∧ Q
          -- (h.1 ⟨p, q⟩).1 : R
          (λ p ↦ (h.1 ⟨p, q⟩).1)
          -- r : R
          -- ⟨r, q⟩ : R ∧ Q
          -- h.2 : R ∧ Q → P ∧ Q
          -- h.2 ⟨r, q⟩ : P ∧ Q
          -- (h.2 ⟨r, q⟩).1 : P
          (λ r ↦ (h.2 ⟨r, q⟩).1)
  have y : (Q → (P ↔ R)) → (P ∧ Q ↔ R ∧ Q) :=
    λ
      h ↦
        Iff.intro
          -- q : Q
          -- h q : P ↔ R
          -- (h q).1 p : R
          -- ⟨(h q).1 p, q⟩ : R ∧ Q
          (λ ⟨p, q⟩ ↦ ⟨(h q).1 p, q⟩)
          -- q : Q
          -- h q : P ↔ R
          -- (h q).2 r : P
          -- ⟨(h q).2 r, q⟩ : P ∧ Q
          (λ ⟨r, q⟩ ↦ ⟨(h q).2 r, q⟩)
  exact Iff.intro x y

theorem imp_trans (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  have x : C → S := λ c ↦ h2 (h1 c)
  exact x

example (L : Prop) : ¬(L ∧ ¬L) := by
  have x : ¬(L ∧ ¬L) := λ ⟨l, m⟩ ↦ False.elim (m l)
  exact x

example (B S : Prop) (h1 : B → S) (h2 : ¬S) : ¬B := by
  have x : ¬B := λ b ↦ False.elim (h2 (h1 b))
  exact x

theorem modus_tollens (h : P → Q) (nq : ¬Q) : ¬P := (λ p ↦ (nq ∘ h) p)

example (A : Prop) (h: A → ¬A) : ¬A := by
  -- h : A → ¬A = A → A → False
  have α : A → False := λ a ↦ h a a
  have x : A → False := λ a ↦ False.elim (h a a)
  exact x

example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  -- h : ¬(B → C) = (B → C) → False
   have h₁ : C → False := fun hc => h fun _ => hc
   exact h₁

example (P : Prop) : ¬(P ∧ ¬P) := by
  intro pnp
  cases pnp
  contradiction
