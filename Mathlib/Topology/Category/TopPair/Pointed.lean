/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Pointed
public import Mathlib.Topology.Category.TopPair.Basic

/-!
# Pointed topological pairs

In this file, we introduce the category of pointed topological pairs.
-/

@[expose] public section

open CategoryTheory TopPair Opposite

universe u

namespace TopPair

/-- A pair of poitned topological spaces consists of an embedding `f : A ⟶ X` in `TopCat.Pointed`.
-/
abbrev Pointed :=
  MorphismProperty.Arrow TopCat.Pointed.isEmbedding ⊤ ⊤

namespace Pointed

variable {Xₚ Yₚ : Pointed.{u}}

/-- The first space of the pointed pair -/
abbrev fst : TopCat.Pointed.{u} := Xₚ.right

/-- The second space of the pointed pair -/
abbrev snd : TopCat.Pointed.{u} := Xₚ.left

/-- The embedding of the second into the first pointed space -/
abbrev map : Xₚ.snd ⟶ Xₚ.fst := Xₚ.hom

lemma isEmbedding_map (X : Pointed.{u}) : Topology.IsEmbedding X.map.hom := X.prop

/-- Construct a pointed topological pair from its components. -/
abbrev of {A X : TopCat.Pointed.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f.hom) : Pointed.{u} :=
  MorphismProperty.Arrow.mk (P := TopCat.Pointed.isEmbedding) f h

/-- Construct a morphism in `TopPair.Pointed` from its components. -/
abbrev ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd)
    (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

/-- The map between the first pointed spaces. -/
abbrev Hom.fst (f : Xₚ ⟶ Yₚ) : Xₚ.fst ⟶ Yₚ.fst := f.hom.right

@[simp]
lemma Hom.fst_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd)
    (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) : Hom.fst (ofHom f g) = f := rfl

/-- The map between the second pointed spaces. -/
abbrev Hom.snd (f : Xₚ ⟶ Yₚ) : Xₚ.snd ⟶ Yₚ.snd := f.hom.left

@[simp]
lemma Hom.snd_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd)
    (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) : Hom.snd (ofHom f g) = g := rfl

@[reassoc, elementwise]
lemma Hom.w (f : Xₚ ⟶ Yₚ) :
    Hom.snd f ≫ Yₚ.map = Xₚ.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

/-- Turn a pointed topological pair into an unpointed topological pair. -/
def toTopPair (Xₚ : Pointed.{u}) : TopPair.{u} := TopPair.of Xₚ.map.toTopCatHom sorry

/-- Turn a morphism of pointed topological pairs into a morphism of unpointed topological pairs. -/
def Hom.toTopPairHom {Xₚ Yₚ : Pointed.{u}} (f : Xₚ ⟶ Yₚ) : (Xₚ.toTopPair ⟶ Yₚ.toTopPair) :=
  TopPair.ofHom (Hom.fst f).toTopCatHom (Hom.snd f).toTopCatHom sorry

instance : Coe Pointed.{u} TopPair.{u} where
  coe := toTopPair

instance {Xₚ Yₚ : Pointed.{u}} : Coe (Xₚ ⟶ Yₚ) ((Xₚ : TopPair) ⟶ Yₚ) where
  coe := Hom.toTopPairHom

/-- The forgetful functor from pointed topological pairs to unpointed topological pairs. -/
abbrev forget : Pointed.{u} ⥤ TopPair.{u} where
  obj X := X
  map f := f

/-- The functor from pointed topological pairs to pointed topological spaces that forgets the second
space, i.e. the projection to the first space. -/
def proj₁ : Pointed.{u} ⥤ TopCat.Pointed.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

-- `simps` generates the wrong lemmas
@[simp]
lemma proj₁_obj (Xₚ : Pointed.{u}) : proj₁.obj Xₚ = Xₚ.fst := rfl

@[simp]
lemma proj₁_map (f : Xₚ ⟶ Yₚ) : proj₁.map f = Hom.fst f := rfl

/-- The functor from pointed topological pairs to pointed topological spaces that forgets the first
space, i.e. the projection to the second space. -/
def proj₂ : Pointed.{u} ⥤ TopCat.Pointed.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

-- simps generates the wrong lemmas
@[simp]
lemma proj₂_obj (Xₚ : Pointed.{u}) : proj₂.obj Xₚ = Xₚ.snd := rfl

@[simp]
lemma proj₂_map (f : Xₚ ⟶ Yₚ) : proj₂.map f = Hom.snd f := rfl

-- simps generates the wrong lemmas
@[simp]
lemma proj₂_op_obj (Xₚ : Pointed.{u}ᵒᵖ) : (proj₂.op.obj Xₚ) = op Xₚ.unop.snd := rfl

@[simp]
lemma proj₂_op_map {Xₚ Yₚ : Pointed.{u}ᵒᵖ} (f : Xₚ ⟶ Yₚ) : (proj₂.op.map f) = (Hom.snd f.unop).op :=
  rfl

/-- Unpointed and pointed projection and forgetting are compatible. -/
def proj₁ForgetIso : proj₁ ⋙ TopCat.Pointed.forget ≅ forget ⋙ TopPair.proj₁ := Iso.refl _

/-- Unpointed and pointed projection and forgetting are compatible. -/
def proj₂ForgetIso : proj₂ ⋙ TopCat.Pointed.forget ≅ forget ⋙ TopPair.proj₂ := Iso.refl _

end Pointed

end TopPair
