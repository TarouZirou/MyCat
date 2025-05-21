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
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.Category.Grp.Basic



open CategoryTheory
open CategoryTheory Opposite

attribute [simp] CategoryStruct.id CategoryStruct.comp
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

section Test
variable (A B C D : Type*) (f : A → B) (g : B → C) (x : A)
example : (λ x ↦ f x) x = f x := by
  exact rfl

variable [Category A] (a b c : A) (f : a ⟶ b) (g : b ⟶ c)
#check f ≫ g

end Test

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

section Hom
universe u₁ u₂
/-- Hom (-,X) -/
instance HomInv {C : Type u₁} [Category C] (X : C) : Cᵒᵖ ⥤ Type* where
  obj (Y : Cᵒᵖ) := Quiver.Hom (unop Y) X
  map {Y X : Cᵒᵖ} f g := f.unop ≫ g
  map_id := by
    intro X
    funext g
    simp only [CategoryStruct.id, Quiver.Hom.unop_op]
    simp
  map_comp := by
    intro X Y Z f g
    funext h
    simp only [CategoryStruct.comp, Quiver.Hom.unop_op]
    have h' : ((fun g_1 ↦ g.unop ≫ g_1) ∘ fun g ↦ f.unop ≫ g) h = g.unop ≫ (f.unop ≫ h) := rfl
    rw [h']
    simp

/-- Hom (X,-) -/
instance HomTo {C : Type u₁} [Category C] (X : C) : C ⥤ Type* where
  obj (Y : C) := Quiver.Hom X Y
  map {X Y : C} f g := g ≫ f

instance Hom {C : Type u₁} [Category C] : Cᵒᵖ × C ⥤ Type* where
  obj X := Quiver.Hom X.1.unop X.2
  map {X Y : Cᵒᵖ × C} f g := f.1.unop ≫ g ≫ f.2
  map_id := by
    intro X
    funext f
    simp only [CategoryStruct.id, Quiver.Hom.unop_op, Category.id_comp, Category.comp_id]
  map_comp := by
    intro X Y Z f g
    funext h
    simp only [CategoryStruct.comp, Quiver.Hom.unop_op]
    have h' :
      ((fun g_1 ↦ g.1.unop ≫ g_1 ≫ g.2) ∘ fun g ↦ f.1.unop ≫ g ≫ f.2) h
      = g.1.unop ≫ (f.1.unop ≫ h ≫ f.2) ≫ g.2 := rfl
    rw [h']
    simp [Category.assoc]

end Hom

section Curry
universe u₁ u₂ u₃

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) [Category A] [Category B] [Category C]
variable (b : B)

/-
instance : Category (A × B) where
  Hom a b := Hom a.1 a.2  Hom b.1 b.2

def t (B : Type*) [Category B]: Cat ⥤ Cat where
  obj A := A × B
-/

end Curry
