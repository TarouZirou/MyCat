import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Category.Grp.Basic



open CategoryTheory
open CategoryTheory Opposite

attribute [simp] CategoryStruct.id CategoryStruct.comp
attribute [simp] Category.comp_id Category.id_comp
attribute [simp] Quiver.Hom Quiver.symmetrifyQuiver
attribute [simp] Functor.Comp.lawfulFunctor
attribute [simp] NatTrans.naturality

section Grp
universe u₁ u₂

variable {G : Type u₁} [Group G] {H : Type u₂} [Group H]
variable (g : G) {α : H}
variable (f k: G →* H) (h : ∀ x : G, α * f x * α⁻¹ = k x)
variable (U : Type u₂)

@[simp]
def GroupFunc : SingleObj G ⥤ SingleObj H where
  obj (_ : SingleObj G) := SingleObj.star H
  map {X Y : SingleObj G} (g : X ⟶ Y) : (SingleObj.star H ⟶ SingleObj.star H) := f g

@[simp]
def GroupNatTrans : NatTrans (GroupFunc f) (GroupFunc k) where
  app (_ : SingleObj G) := α
  naturality := by
    intro _ _ x
    simp
    exact mul_inv_eq_iff_eq_mul.mp (h x)

end Grp

section Adj
universe u₁

variable (G' : Type u₁) [Group G'] (H' : Type u₁) [Group H']
variable (f' : G' →* H') (k' : H' →* G') (h' : k' ∘ f' = MonoidHom.id _ ∧ f' ∘ k' = MonoidHom.id _)
variable (φ : SingleObj G' ≅ SingleObj H')

#check MonoidHom.id

@[simp]
def unit : 𝟭 (SingleObj G') ⟶ (GroupFunc f') ⋙ (GroupFunc k') where
  app X := 1
  naturality := by
    intro _ _ f
    simp [GroupFunc]
    rw [← @Function.comp_apply _ _ _ k' f',h'.left, MonoidHom.id_apply]

@[simp]
def counit : (GroupFunc k') ⋙ (GroupFunc f') ⟶ 𝟭 (SingleObj H') where
  app Y := 1
  naturality := by
    intro _ _ f
    simp [GroupFunc]
    rw [← @Function.comp_apply _ _ _ f' k', h'.right, MonoidHom.id_apply]

def GroupAdjunction : Adjunction (GroupFunc f') (GroupFunc k') where
  unit := unit G' H' f' k' h'
  counit := counit G' H' f' k' h'

end Adj

section Set

instance : Category Type* where
  Hom a b := a → b
  id a := λ x ↦ x
  comp f g := g ∘ f

instance : Category Prop where
  Hom P Q := PLift (P → Q)
  id P := PLift.up (id)
  comp {P Q R : Prop} h h' := PLift.up (λ p ↦ h'.down (h.down p))

end Set

section Props

variable (P Q : Prop)

def π₁ : P ∧ Q → P := λ ⟨p, _⟩ ↦ p
def π₂ : P ∧ Q → Q := λ ⟨_, q⟩ ↦ q
axiom x (X : Prop) : X → (P ∧ Q)
def f₁ (X : Prop) : X → P := (π₁ P Q) ∘ (x P Q X)
def f₂ (X : Prop) : X → Q := (π₂ P Q) ∘ (x P Q X)

instance (P Q R : Prop) : Iso (Quiver.Hom (P ∧ Q) R) (Quiver.Hom P (Q → R)) where
  hom := by
    intro h
    simp [Quiver.Hom]
    apply PLift.pure
    simp [Quiver.Hom] at h
    apply PLift.down at h
    exact h
  inv := by
    intro h
    simp [Quiver.Hom]
    apply PLift.pure
    simp [Quiver.Hom] at h
    apply PLift.down at h
    exact h
  hom_inv_id := by
    funext h
    simp [Quiver.Hom] at h
    apply PLift.down at h
    simp only [Quiver.Hom, CategoryStruct.comp, CategoryStruct.id, Function.comp_apply]
    exact PLift.down_inj.mp rfl

end Props


section Curry
universe u₁ u₂ u₃

variable (A : Type u₂) (B : Type u₂) (C : Type u₂) [Category A] [Category B] [Category C]

/-
instance Product : Category (A × B) where
  Hom x x' := (Quiver.Hom x.1 x'.1) × (Quiver.Hom x.2 x'.2)
  id x := ⟨CategoryStruct.id x.1, CategoryStruct.id x.2⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, f.2 ≫ g.2⟩
-/
universe u v



end Curry
