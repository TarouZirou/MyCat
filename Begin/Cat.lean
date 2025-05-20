import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.CategoryTheory.Category.Basic

namespace MyCat

universe u

/-- 圏の定義 -/
class Category (C : Type*) where
  /-- ホム集合 -/
  Hom : C → C → Type*
  /-- 合成 -/
  comp {a b c : C} :  Hom a b → Hom b c → Hom a c
  /-- 恒等射 -/
  id (a : C) : Hom a a
  /-- 始域 -/
  dom {a b : C} (f : Hom a b) := a
  /-- 終域 -/
  cod {a b : C} (f : Hom a b) := b
  /-- 恒等射の性質-/
  id_comp {a b : C} (f : Hom a b) : comp (id a) f = f := by aesop
  /-- 恒等射の性質-/
  comp_id {a b : C} (f : Hom a b) : comp f (id b) = f := by aesop
  /-- 合成の結合法則 -/
  assoc {a b c d : C} (f : Hom a b) (g : Hom b c) (h : Hom c d) :
    comp (comp f g) h = comp f (comp g h) := by aesop

variable (C : Type*) [Category C]

#check Cᵒᵖ

open Category

/-- 合成の簡略化 -/
infixr:80 "⟫" => comp

/-- 恒等射の簡略化 -/
notation "𝟙" => Category.id

attribute [simp] id_comp comp_id assoc

/-- 関手 -/
class Func (C : Type*) [Category C] (D : Type*) [Category D] where
  /-- 対象の変換 -/
  obj : C → D
  /-- 射の変換 -/
  map {a b : C} : Hom a b → Hom (obj a) (obj b)
  /-- 恒等射の変換は、変換された対象の恒等射に等しい -/
  map_id {a : C} : map (𝟙 a) = 𝟙 (obj a) := by aesop
  /-- 合成された射の変換は、変換された射の合成に等しい -/
  map_comp {a b c : C} (f : Hom a b) (g : Hom b c): map (f ⟫ g) = map f ⟫ map g := by aesop

/-
/-- 反変関手 -/
class OppFunc (C D : Type*) [Category C] [Category D] where
  obj : C → D
  map {a b : C} : Hom a b → Hom (obj b) (obj a)
  map_id {a : C} : map (𝟙 a) = 𝟙 (obj a) := by aesop
  map_comp {a b c : C} (f : Hom a b) (g : Hom b c) : map (f ⟫ g) = map g ⟫ map f := by aesop
-/

infixr:80 "⥤" => Func

open Func

attribute [simp] map_id map_comp

/-- 自然変換 -/
class NatTrans {C : Type*} {D : Type*} [Category C] [Category D] (F G : C ⥤ D) where
  /-- F(f) → G(f) -/
  app (a : C) : Hom (F.obj a) (G.obj a)
  /-- φ(b) ∘ F(f) = G(f) ∘ φ(a) -/
  nat (a b : C) (f : Hom a b) : F.map f ⟫ app b = app a ⟫ G.map f := by aesop

/--/
/-- 反変関手の自然変換 -/
class OppNatTrans {C : Type*} {D : Type*} [Category C] [Category D] (F G : OppFunc C D) where
  /-- F(f) → G(f) -/
  app (a : C) : Hom (F.obj a) (G.obj a)
  /-- φ(b) ∘ F(f) = G(f) ∘ φ(a) -/
  nat (a b : C) (f : Hom a b) : app b ⟫ G.map f = F.map f ⟫ app a := by aesop
-/

infixr:80 "⟶" => NatTrans

open NatTrans

attribute [simp] nat

inductive Opp (C : Type u) : Type u
  | mk : C → Opp C
postfix:max "ᵒᵖ" => Opp

namespace Opp

/-- 元に戻す動作 -/
def unop {C : Type*} : Opp C → C
  | mk c => c

/-- 反転させる動作 -/
def op {C : Type*} : C → Opp C
  | c => mk c

instance {C : Type u} [Category C] : Category (Opp C) where
  Hom a b := Hom (unop b) (unop a)
  comp f g := comp g f
  id := (λ a ↦ id (unop a))

def op_map {C : Type*} [Category C] {A B : C} (f : Hom A B) :
  Hom (mk B) (mk A) := f

end Opp

abbrev OppFunc (C D : Type*) [Category C] [Category D] := Func (Opp C) D
infixr:80 "ᵒᵖ⥤" => OppFunc
abbrev OppNatTrans {C D : Type*} [Category C] [Category D] (F G : C ᵒᵖ⥤ D) := F ⟶ G

/-- 自分自身への反変関手 -/
instance (C : Type*) [Category C]: C ᵒᵖ⥤ Opp C where
  obj a := a
  map f := f

/-- 同型 -/
class Isom {C : Type*} [Category C] (a b : C) where
  to_arrow : Hom a b
  inv_arrow : Hom b a
  to_inv : to_arrow ⟫ inv_arrow = 𝟙 a := by aesop
  inv_to : inv_arrow ⟫ to_arrow = 𝟙 b := by aesop
infix:20 "≅" => Isom
attribute [simp] Isom.to_inv Isom.inv_to

/-- 自己同型 -/
instance SelfIsom {C : Type*} [Category C] (a : C) : Isom a a where
  to_arrow := id a
  inv_arrow := id a

/--
集合の圏
随伴で、ホム集合の同型を定義するために必要となる
-/
instance Set : Category Type* where
  Hom a b := a → b
  comp f g := g ∘ f
  id a := id

/-- 随伴 -/
class Adj (C : Type*) (D : Type*) [Category C] [Category D] where
  L : C ⥤ D
  R : D ⥤ C
  hom_isom (c : C) (d : D) : Isom (Hom (L.obj c) d) (Hom c (R.obj d))

/-- 関手圏 -/
instance FuncCat (C : Type*) (D : Type*) [Category C] [Category D] : Category (C ⥤ D) where
  Hom F G := F ⟶ G
  comp {F G H} (α : F ⟶ G) (β : G ⟶ H) : F ⟶ H := {
    app a := α.app a ⟫ β.app a
    nat a b f := by
      rw [← assoc]
      rw [NatTrans.nat]
      rw [assoc]
      rw [NatTrans.nat]
      simp
  }
  id F := {
    app a := 𝟙 (F.obj a)
  }

/-- 反変関手の圏 -/
instance OppFuncCat (C : Type*) (D : Type*) [Category C] [Category D] : Category (C ᵒᵖ⥤ D) where
  Hom F_op G_op := OppNatTrans F_op G_op
  comp {F G H} (α : OppNatTrans F G) (β : OppNatTrans G H) : OppNatTrans F H := {
    app a := α.app a ⟫ β.app a
    nat a b f := by
      rw [← assoc]
      rw [NatTrans.nat]
      rw [assoc]
      rw [NatTrans.nat]
      simp
  }
  id F := {
    app a := 𝟙 (F.obj a)
  }
structure GroupCat where
  base : Type*
  str : Group base

instance : CoeSort GroupCat Type* := ⟨fun R ↦ R.base⟩
instance (R : GroupCat) : Group R.base := R.str

instance Grp : Category GroupCat where
  Hom G H := G →* H
  comp f g := MonoidHom.comp g f
  id G := MonoidHom.id G

structure CatCat where
  base : Type*
  str : Category base

instance : CoeSort CatCat Type := ⟨fun G => G.base⟩
instance (G : CatCat) : Category G.base := G.str

/-- 圏の圏 -/
instance Cat : Category CatCat where
  Hom a b := a ⥤ b
  comp {a b c} F G := {
    obj := G.obj ∘ F.obj
    map := G.map ∘ F.map
  }
  id a := {
    obj a := a
    map := id
  }

/-- 前順序集合 -/
class PreOrd (C : Type*) where
  le : C → C → Prop
  refl (x : C) : le x x := by aesop
  trans {x y z : C} : le x y → le y z → le x z := by aesop

/-- 順序集合 -/
class PartialOrd (C : Type*) extends PreOrd C where
  antisymm {x y : C} : le x y → le y x → x = y := by aesop

/-- 自然数の順序集合の例 -/
instance OrdNat : PartialOrd Nat where
  le x y := x <= y
  refl x : x <= x := Nat.le_refl x
  trans := fun a b ↦ Nat.le_trans a b
  antisymm := fun a b ↦ Nat.le_antisymm a b

/-- 順序集合が圏であることの証明 -/
instance PreOrdCat (C : Type u) [PreOrd C] : Category C where
  Hom a b:= PLift (PreOrd.le a b)
  comp {a b c : C} f g := PLift.up (PreOrd.trans f.down g.down)
  id a := PLift.up (PreOrd.refl a)
