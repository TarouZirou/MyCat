import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic

/- 対象全体の集合の属する階層 -/
universe u

/- ホム集合の属する階層 -/
universe v

namespace MyCat

/-- 圏の定義 -/
class Category (C : Type u) where
  /-- ホム集合 -/
  Hom : C → C → Type v
  /-- 合成 -/
  comp {a b c : C} :  Hom a b → Hom b c → Hom a c
  /-- 恒等写像 -/
  id (a : C) : Hom a a
  dom {a b : C} (f : Hom a b) := a
  cod {a b : C} (f : Hom a b) := b
  id_comp {a b : C} (f : Hom a b) : comp (id a) f = f := by aesop
  comp_id {a b : C} (f : Hom a b) : comp f (id b) = f := by aesop
  assoc {a b c d : C} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    comp (comp f g) h = comp f (comp g h) := by aesop

open Category

infixr:80 "⟫" => Category.comp

notation "𝟙" => Category.id

attribute [simp] id_comp comp_id assoc

instance : Category Type* where
  Hom a b := a → b
  comp f g := g ∘ f
  id a := id

structure GroupCat where
  base : Type*
  str : Group base

instance : CoeSort GroupCat Type := ⟨fun R ↦ R.base⟩
instance (R : GroupCat) : Group R.base := R.str

instance : Category GroupCat where
  Hom G H := G →* H
  comp f g := MonoidHom.comp g f
  id G := MonoidHom.id G

--instance : CoeSort OppositeCat Type := ⟨fun R ↦ R.base⟩
--instance (R : OppositeCat) : Category R.base := R.str


inductive Opp (C : Type u) : Type u
  | mk : C → Opp C

namespace Opp

/-- 元に戻す動作 -/
def unop {C : Type u} : Opp C → C
  | mk c => c

/-- 反転させる動作 -/
def op {C : Type u} : C → Opp C
  | c => mk c

instance {C : Type u} [Category.{u, v} C] : Category.{u, v} (Opp C) where
  Hom a b := Hom (unop b) (unop a)
  comp f g := comp g f
  id := (λ a ↦ id (unop a))

end Opp

universe u₁ v₁ u₂ v₂

structure Functor (C : Type u₁) [Category.{u₁,v₁} C] (D : Type u₂) [Category.{u₂,v₂} D] where
  obj : C → D
  map {a b : C} : Hom a b → Hom (obj a) (obj b)
  map_id {a : C} : map (𝟙 a) = 𝟙 (obj a)
  map_comp {a b c : C} (f : Hom a b) (g : Hom b c): map (f ⟫ g) = map f ⟫ map g

--instance (C : Type u₁) [Category.{u₁, v₁} C]: Functor C (Opp C) where
