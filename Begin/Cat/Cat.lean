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

def F : Cat ⥤ Cat where
  obj A := Cat.of (A × B)
  map {X Y} (f : X ⥤ Y) := f.prod (𝟭 B)

def G : Cat ⥤ Cat where
  obj A := Cat.of (B ⥤ A)
  map {X Y} F :=
    (whiskeringRight B X Y).obj F

def α (a : A) (f : A × B ⥤ C): B ⥤ C := {
    obj b := f.obj ⟨a, b⟩
    map {b b'} x₂ := f.map ⟨𝟙 a, x₂⟩
    map_id := by
      intro b
      rw [← prod_id, f.map_id]
    map_comp := by
      intro b b' b'' x₂1 x₂2
      set u : (a, b) ⟶ (a, b') := ⟨𝟙 a, x₂1⟩ with hu
      set v : (a, b') ⟶ (a, b'') := ⟨𝟙 a, x₂2⟩ with hv
      have h₁ : u ≫ v = ⟨𝟙 a ≫ 𝟙 a, x₂1 ≫ x₂2⟩ := rfl
      rw [← Category.id_comp (𝟙 a)]
      rw [← h₁]
      rw [f.map_comp]
  }

def β {a a' : A} (f : A × B ⥤ C) (x₁ : a ⟶ a') : NatTrans (α A B C a f) (α A B C a' f) := {
    app b := f.map ⟨x₁, 𝟙 b⟩
    naturality := by
      intro b' b'' x₂
      simp
      dsimp only [α]
      set u : (a, b') ⟶ (a, b'') := ⟨𝟙 a, x₂⟩ with hu
      set v : (a', b') ⟶ (a', b'') := ⟨𝟙 a', x₂⟩ with hv
      set w : (a, b'') ⟶ (a', b'') := ⟨x₁, 𝟙 b''⟩ with hw
      set x : (a, b') ⟶ (a', b') := ⟨x₁, 𝟙 b'⟩ with hx
      --have h₁ : ∀ a:A,∀ x,(α A B C a f).map x = f.map ⟨𝟙 a, x⟩ := by
      simp [← f.map_comp]
      simp only [hu, hv, hw, hx]
      simp only [Category.id_comp,Category.comp_id]
  }

def Φ (f : A × B ⥤ C) : A ⥤ (B ⥤ C) where
  obj a := α A B C a f
  map {a a'} x₁  := β A B C f x₁
  map_id := by
    intro X
    simp
    apply NatTrans.ext
    funext z
    simp [NatTrans.id_app']
    dsimp only [α, β]
    rw [← prod_id]
    rw [f.map_id]
  map_comp := by
    intro a a' a'' x₁1 x₁2
    --dsimp only [β]
    apply NatTrans.ext
    funext b
    rw [NatTrans.comp_app]
    dsimp only [β]
    set u : (a, b) ⟶ (a', b) := ⟨x₁1, 𝟙 b⟩ with hu
    set v : (a', b) ⟶ (a'', b) := ⟨x₁2, 𝟙 b⟩ with hv
    have h₁ : u ≫ v = ⟨x₁1 ≫ x₁2, 𝟙 b ≫ 𝟙 b⟩ := rfl
    rw [← Category.comp_id (𝟙 b)]
    rw [← h₁]
    rw [f.map_comp]

def Ψ (g : A ⥤ (B ⥤ C)) : A × B ⥤ C where
  obj ab := (g.obj ab.1).obj ab.2
  map {ab ab'} xy := (g.obj ab.1).map xy.2 ≫ (g.map xy.1).app ab'.2
  map_comp := by
    intro ab ab' ab'' x x'
    have h₁ : (x ≫ x').1 = (x.1 ≫ x'.1) := rfl
    have h₂ : (x ≫ x').2 = (x.2 ≫ x'.2) := rfl
    simp only [h₁, h₂]
    simp only [Functor.map_comp]
    simp only [NatTrans.vcomp_app']
    simp

def CurIso :
  (Cat.of ((F B).obj (Cat.of A)) ⟶ Cat.of C) ≅
  (Cat.of A ⟶ Cat.of ((G B).obj (Cat.of C))) where
  hom := Φ A B C
  inv := Ψ A B C
  hom_inv_id := by
    ext F
    simp
    refine Functor.hext (congrFun rfl) ?_
    intro ab ab' x
    simp [Φ, Ψ, β, α]
    set u : (ab.1, ab.2) ⟶ (ab.1, ab'.2) := ⟨𝟙 ab.1, x.2⟩ with hu
    set v : (ab.1, ab'.2) ⟶ (ab'.1, ab'.2) := ⟨x.1, 𝟙 ab'.2⟩ with hv
    have h₁ : u ≫ v = ⟨𝟙 ab.1 ≫ x.1, x.2 ≫ 𝟙 ab'.2⟩ := rfl
    rw [← F.map_comp]
    rw [h₁]
    simp
  inv_hom_id := by
    refine
      types_ext (Ψ A B C ≫ Φ A B C) (𝟙 (Cat.of A ⟶ Cat.of ↑((G B).obj (Cat.of C)))) ?_
    intro F
    simp
    refine Functor.hext ?_ ?_
    intro a
    set ΦΨF := (Φ A B C (Ψ A B C F)) with hΦΨ
    have h₁ : ∀ a,(ΦΨF.obj a = F.obj a) := by
      intro a
      simp [hΦΨ, Ψ, Φ, α]
    exact h₁ a
    intro a a' x₁
    set ΦΨF := (Φ A B C (Ψ A B C F)) with hΦΨ
    have h₁ : ∀ a,(ΦΨF.obj a = F.obj a) := by
      intro a
      simp [hΦΨ, Ψ, Φ, α]
    --simp [Ψ, Φ, β] at hΦΨ
    set Fx₁ := F.map x₁ with hFx₁
    have h₂ :
      (F.obj a ⟶ F.obj a') = (ΦΨF.obj a ⟶ ΦΨF.obj a') := by
      rw [← h₁ a, ← h₁ a']
    rw [h₂] at Fx₁
    sorry


/-
instance : Adjunction.CoreHomEquiv (F B) (G B) where
  homEquiv X Y := {

  }
-/

end Curry
