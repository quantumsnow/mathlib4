module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Topology.Category.TopCat.HomologyCategory

@[expose] public section

open CategoryTheory TopCat Limits

universe u

namespace TopCat

structure Pointed extends TopCat.{u} where
  of ::
  basepoint : carrier

attribute [coe] Pointed.toTopCat

instance : Coe Pointed.{u} TopCat.{u} where
  coe := Pointed.toTopCat

namespace Pointed

variable (X Y : Pointed.{u})

-- TODO: make this special case of `TopPair` (eg subcategory)?
structure Hom extends toTopCatHom : TopCat.Hom X Y where
  ofHom ::
  hom_point : toTopCatHom.hom X.basepoint = Y.basepoint := by cat_disch

export Hom (ofHom)

instance : Category Pointed.{u} where
  Hom := Hom
  id _ := { toTopCatHom := TopCat.instCategory.id _ }
  comp f g := { toTopCatHom := TopCat.instCategory.comp f.toTopCatHom g.toTopCatHom, hom_point := by simp [f.hom_point, g.hom_point] }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

attribute [coe] Hom.toTopCatHom

instance {X Y : Pointed.{u}} : Coe (X ⟶ Y) ((X : TopCat) ⟶ Y) where
  coe := Hom.toTopCatHom

def forget : Pointed.{u} ⥤ TopCat.{u} where
  obj X := X
  map f := f

def forgetArrow : Arrow Pointed.{u} ⥤ Arrow TopCat.{u} where
  obj a := Arrow.mk a.hom.toTopCatHom
  map f := Arrow.homMk f.left.toTopCatHom f.right.toTopCatHom <| by
    have := f.w
    simp [f.w]
    sorry

-- /-- The terminal object of `Top.Pointed` is `PUnit`. -/
-- def isTerminalPUnit : IsTerminal (of (TopCat.of PUnit.{u + 1}) PUnit.unit) :=
--   haveI : ∀ X, Unique (X ⟶ of (TopCat.of PUnit.{u + 1}) PUnit.unit) := fun X =>
--     ⟨⟨TopCat.isTerminalPUnit.from X, by simp⟩, sorry⟩
--   Limits.IsTerminal.ofUnique _

/-- The initial object of `Top.Pointed` is `PUnit`. -/
def isInitialPUnit : IsInitial (of (TopCat.of PUnit.{u + 1}) PUnit.unit) := sorry

-- instance : HasPushouts Pointed.{u} := sorry

abbrev isEmbedding : MorphismProperty Pointed :=
  fun ⦃A X : Pointed⦄ (f : A ⟶ X) ↦ Topology.IsEmbedding f.hom

/-- The interval with basepoint `i`. -/
def I (i : I) : Pointed.{u} := ⟨TopCat.I, i⟩

def pointedProperty : ObjectProperty TopCat.{u} → ObjectProperty Pointed.{u} := fun P X ↦ P X

def isCompact : ObjectProperty Pointed.{u} := pointedProperty TopCat.isCompact

abbrev HomologyCategory (P : ObjectProperty TopCat.{u}) [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderFiniteCoproducts] := (pointedProperty P).FullSubcategory

namespace HomologyCategory

open ObjectProperty

variable (P : ObjectProperty TopCat.{u}) [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderFiniteCoproducts]

def forget :
    HomologyCategory P ⥤ TopCat.HomologyCategory P where
  obj X := ⟨X.obj.toTopCat, X.property⟩
  map f := ⟨f.hom.toTopCatHom⟩

def isClosedUnderTerminal {X : Pointed.{u}} (h : IsTerminal X) : P X := sorry

def isClosedUnderInitial {X : Pointed.{u}} (h : IsInitial X) : P X := sorry

def singleton : HomologyCategory P where
  obj := ⟨(TopCat.HomologyCategory.singleton P).obj, PUnit.unit⟩
  property := isClosedUnderInitial P TopCat.Pointed.isInitialPUnit

def isTerminalPUnit : IsTerminal (singleton P) := sorry
  -- haveI : ∀ X, Unique (X ⟶ TopCat.of PUnit.{u + 1}) := fun X =>
  --   ⟨⟨ofHom ⟨fun _ => PUnit.unit, continuous_const⟩⟩, fun f => by ext⟩
  -- Limits.IsTerminal.ofUnique _

def isInitialPUnit : IsInitial (singleton P) := sorry
  -- haveI : ∀ X, Unique (TopCat.of PEmpty.{u + 1} ⟶ X) := fun X =>
  --   ⟨⟨ofHom ⟨fun x => x.elim, by fun_prop⟩⟩, fun f => by ext ⟨⟩⟩
  -- Limits.IsInitial.ofUnique _

/-- The `MorphismProperty` in a full subcategory of `TopCat` that a morphism is an embedding. -/
abbrev isEmbedding : MorphismProperty (HomologyCategory P) :=
  fun ⦃A X : HomologyCategory P⦄ (f : A ⟶ X) ↦ TopCat.isEmbedding f.hom.toTopCatHom

end HomologyCategory

end Pointed

end TopCat
