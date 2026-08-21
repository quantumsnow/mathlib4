/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Pointed topological spaces

In this file, we introduce the category of pointed topological spaces.
-/

@[expose] public section

open CategoryTheory TopCat Limits

universe u

namespace TopCat

/-- A pointed topological space is a topological space with a chosen basepoint. -/
structure Pointed extends TopCat.{u} where
  of ::
  /-- The basepoint of a pointed topological space. -/
  basepoint : carrier

attribute [coe] Pointed.toTopCat

instance : Coe Pointed.{u} TopCat.{u} where
  coe := Pointed.toTopCat

namespace Pointed

variable (X Y : Pointed.{u})

/-- A morphism of pointed topological spaces is a morphism of topological spaces that maps the
basepoint to the basepoint. -/
structure Hom extends toTopCatHom : TopCat.Hom X Y where
  ofHom ::
  hom_point : toTopCatHom.hom X.basepoint = Y.basepoint := by cat_disch

export Hom (ofHom)

instance : Category Pointed.{u} where
  Hom := Hom
  id _ := { toTopCatHom := TopCat.instCategory.id _ }
  comp f g := Pointed.ofHom (TopCat.instCategory.comp f.toTopCatHom g.toTopCatHom) <| by
    simp [f.hom_point, g.hom_point]

attribute [coe] Hom.toTopCatHom

instance {X Y : Pointed.{u}} : Coe (X ⟶ Y) ((X : TopCat) ⟶ Y) where
  coe := Hom.toTopCatHom

/-- The forgetful functor from pointed topological spaces to unpointed topological spaces. -/
def forget : Pointed.{u} ⥤ TopCat.{u} where
  obj X := X
  map f := f

/-- The forgetful functor from arrows pointed topological spaces to arrows of unpointed topological
spaces. -/
def forgetArrow : Arrow Pointed.{u} ⥤ Arrow TopCat.{u} where
  obj a := Arrow.mk a.hom.toTopCatHom
  map f := Arrow.homMk f.left.toTopCatHom f.right.toTopCatHom sorry

/-- The initial object of `Top.Pointed` is `PUnit`. -/
def isInitialPUnit : IsInitial (of (TopCat.of PUnit.{u + 1}) PUnit.unit) := sorry

/-- A morphism of pointed spaces is an embedding if the underlying morphism of unpointed spaces is
an embedding. -/
abbrev isEmbedding : MorphismProperty Pointed :=
  fun ⦃A X : Pointed⦄ (f : A ⟶ X) ↦ Topology.IsEmbedding f.hom

/-- The interval with basepoint `i`. -/
def I (i : I) : Pointed.{u} := ⟨TopCat.I, i⟩

end Pointed

end TopCat
