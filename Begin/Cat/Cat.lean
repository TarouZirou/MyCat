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

variable (A : Type u₁) (B : Type u₂) (C : Type u₃) [Category A] [Category B] [Category C]
variable (b : B)

/-
instance Product : Category (A × B) where
  Hom x x' := (Quiver.Hom x.1 x'.1) × (Quiver.Hom x.2 x'.2)
  id x := ⟨CategoryStruct.id x.1, CategoryStruct.id x.2⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, f.2 ≫ g.2⟩
-/

def F : Cat ⥤ Cat where
  obj A := Cat.of (A × B)
  map {X Y} (f : X ⥤ Y) := f.prod (𝟭 B)

def G : Cat ⥤ Cat where
  obj A := Cat.of (B ⥤ A)
  map {X Y} F :=
    (whiskeringRight B X Y).obj F

instance : Adjunction.CoreHomEquiv (F B) (G B) where
  homEquiv A C := {
    toFun φ := { -- A ⥤ (B ⥤ C)
      -- a : A
      obj a := { -- B ⥤ C
        obj b := φ.obj ⟨a, b⟩
        map {b b'} f := φ.map ⟨CategoryStruct.id a, f⟩
        map_id := by
          intro X
          change φ.map (𝟙 (a, X)) = 𝟙 (φ.obj (a, X))
          rw [φ.map_id]
        map_comp := by
          intro X Y Z f g
          let u : (a, X) ⟶ (a, Y) := ⟨𝟙 a, f⟩
          let v : (a, Y) ⟶ (a, Z) := ⟨𝟙 a, g⟩
          let uv := u ≫ v
          have h₁ : u ≫ v = ⟨𝟙 a ≫ 𝟙 a, f ≫ g⟩ := rfl
          have a₁ : 𝟙 a = 𝟙 a ≫ 𝟙 a := Eq.symm (Category.id_comp (𝟙 a))
          nth_rewrite 1 [a₁]
          rw [← h₁]
          rw [φ.map_comp]
      }
      -- a -f→ a'
      map {a a'} f := { -- natTrans (φa -φf→ φa')
        app b := φ.map ⟨f, 𝟙 b⟩ -- (a ⟶ a') × (b ⟶ b)
        naturality := by
          intro X Y xy
          simp only [prod_id, id_eq, eq_mpr_eq_cast, prod_Hom, prod_comp, cast_eq]
          let u : (a, X) ⟶ (a, Y) := (𝟙 a, xy)
          let v : (a, Y) ⟶ (a', Y) := (f, 𝟙 Y)
          simp only [← φ.map_comp]
          repeat rw [prod_comp]
          simp only [Category.id_comp, Category.comp_id]
      }
      map_id := by
        intros X
        simp only [prod_id, id_eq, eq_mpr_eq_cast, prod_Hom, prod_comp, cast_eq]
        apply NatTrans.ext
        funext β
        set u : B ⥤ C := {
          obj := λ b ↦ φ.obj (X, b)
          map := λ {b b'} f ↦ φ.map (𝟙 X, f)
          map_id := fun X_1 ↦ cast (Eq.symm (congrArg (fun _a ↦ _a = 𝟙 (φ.obj (X, X_1))) (φ.map_id (X, X_1)))) (Eq.refl (𝟙 (φ.obj (X, X_1))))
          map_comp := fun {X_1 Y Z : B} f g ↦ cast
            (Eq.symm
              (congrArg
                (fun _a ↦ φ.map (_a, f ≫ g) = φ.map (𝟙 X, f) ≫ φ.map (𝟙 X, g))
                (Eq.symm (Category.id_comp (𝟙 X)))
              )
            )
            (cast
              (Eq.symm
                (congrArg
                  (fun _a ↦ _a = φ.map (𝟙 X, f) ≫ φ.map (𝟙 X, g))
                  (φ.map_comp (𝟙 X, f) (𝟙 X, g))
                )
              )
              (Eq.refl (φ.map (𝟙 X, f) ≫ φ.map (𝟙 X, g)))
            )
        } with hu
        simp?
        rw [u.map_id]
        rw [← hu]
        rw [Functor.id]
    }
  }

end Curry
