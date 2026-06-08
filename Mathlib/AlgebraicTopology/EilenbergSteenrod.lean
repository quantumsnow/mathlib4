/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/

module

public import Mathlib.Algebra.Homology.ComplexShape
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Category.TopCat.Bicategory
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Eilenberg-Steenrod homology theories

In this file we introduce the Eilenberg-Steenrod axioms for homology theories.

The data for a homology theory is bundled in a structure `HomologyPretheory` consisting of functors
`Hₚ i : TopPair ⥤ C` and `H i : TopCat ⥤ C` which represent the `i`th relative and regular homology,
respectively, (indexed by a `ComplexShape`) and a proof that they agree on `TopCat`. They also
require boundary morphisms `δ i j :  Hₚ i ⟶ proj₂ ⋙ H j` for the long exact sequence of
topological pairs. These are nonzero only if `c.Rel i j`.

We introduce a type class for each axiom. In addition, there are bundled type classes
`IsExtraordinaryEilenbergSteenrod` with the homotopy, excision, additivity, and exactness axioms and
`IsEilenbergSteenrod` on a `HomologyPretheory` on `ComplexShape.down ℕ : ComplexShape ℕ` which
extends the former by the dimension axiom.

Excision is formulated in terms of complements of topological pairs: Suppose `U` and `V` are
complements of a topological pair `X` with embeddings `f : U ⟶ X` and `g : V ⟶ X`. Suppose further
that the closure of `Hom.fst f (U.fst)` is a subset of the interior of the image of `X.snd` in
`X.fst`. Then the excision axiom postulates that the homology of `X` is isomorphic to that of `V`.
Note that this closure condition a priori seems weaker than in the literature. However, we prove
that under these assumptions, `U` is actually an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits TopPair TopCat ObjectProperty

universe u v

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
structure HomologyPretheory
    (C : Type v) [Category C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- The proof that `Hₚ` and `H` agree on `TopCat` -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : (Hₚ i) ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type v} [Category C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι} (i : ι)

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
structure Hom (HP HP' : HomologyPretheory C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `HomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `HomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `HomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : HP.δ i j ≫ proj₂.whiskerLeft (hom j) = homₚ i ≫ HP'.δ i j := by cat_disch

attribute [reassoc (attr := simp)] Hom.iso_comm
attribute [reassoc (attr := local simp)] Hom.w

variable {HP HP' : HomologyPretheory C c}

@[reassoc]
lemma Hom.iso_comm_congr_app (f : HP.Hom HP') (i : ι) (X : TopCat.{u}) :
    dsimp% (HP.iso i).hom.app X ≫ (incl.whiskerLeft (f.homₚ i)).app X =
    (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

@[reassoc]
lemma Hom.w_congr_app (f : HP.Hom HP') (i j : ι) (X : TopPair) :
    dsimp% (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
lemma iso_homₚ_inv_hom (f : HP.Hom HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

@[reassoc (attr := simp)]
lemma iso_homₚ_inv_hom_congr_app (f : HP.Hom HP') (i : ι) (X : TopCat) :
    dsimp% (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X =
    (f.hom i).app X := congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ (f : HP.Hom HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ_congr_app (f : HP.Hom HP') (i : ι) (X : TopCat) :
    dsimp% (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X =
    (f.homₚ i).app (ofTopCat X) := congr($(inv_hom_iso_homₚ _ _).app _)

@[simps]
instance : Category (HomologyPretheory C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
protected def forgetₚ : HomologyPretheory C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

/-- The forgetful functor that sends a `HomologyPretheory` to its homology functor `H`. -/
@[simps]
protected def forget : HomologyPretheory C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

--TODO: rename to reflect target categories other than `Ab` (also rename derived names!)
abbrev coeffGroup [Zero ι] (HP : HomologyPretheory C c) := (HP.H 0).obj (TopCat.of PUnit)

section ReducedHomology

variable (HP) [HasKernels C] (i j : ι) (X : TopCat)

abbrev hToHPUnit := (HP.H i).map (TopCat.isTerminalPUnit.from X)

@[simps]
noncomputable def reducedH : TopCat.{u} ⥤ C where
  obj X := kernel (hToHPUnit HP i X)
  map {X Y} f := kernel.lift (hToHPUnit HP i Y) (kernel.ι (hToHPUnit HP i X) ≫ (HP.H i).map f) <| by
      have : (HP.H i).map f ≫ hToHPUnit HP i Y = hToHPUnit HP i X := by
        rw [← Functor.map_comp]
        cat_disch
      cat_disch

noncomputable def reducedHToH : HP.reducedH i ⟶ HP.H i where
  app X := kernel.ι _

noncomputable abbrev reducedHToHPUnit : (HP.reducedH i).obj X ⟶ (HP.H i).obj (TopCat.of PUnit) :=
  (reducedHToH HP _).app _ ≫ hToHPUnit HP _ _

 --TODO: can make this natural transformation?
abbrev hToReducedHBiprod [HasBinaryBiproducts C] :
    (HP.H i).obj X ⟶ (HP.reducedH i).obj X ⊞ (HP.H i).obj (TopCat.of PUnit) := sorry

instance [HasBinaryBiproducts C] : IsIso (HP.hToReducedHBiprod i X) := sorry

end ReducedHomology

end HomologyPretheory

set_option backward.isDefEq.respectTransparency false in
/-- Under the assumptions of excision, the map of the pair `U` is an isomorphism. -/
lemma isIso_of_isCompl_closure ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
    (hcompl : TopPair.IsCompl f g)
    (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) : IsIso U.map := by
  have surjective_U : Function.Surjective U.map := by
    rw [← Set.range_eq_univ, Set.Subset.antisymm_iff]
    use (by simp)
    rw [← Set.image_subset_image_iff hf.fst.injective]
    have h₀ : Set.range (Hom.fst f) ⊆ Hom.fst f '' Set.range U.map ∪ Hom.fst g '' Set.range V.map :=
      by
      simp only [← Set.range_comp, ← CategoryTheory.hom_comp]
      simp only [← Arrow.w, CategoryTheory.hom_comp, Set.range_comp, ← Set.image_union,
        ← Set.sup_eq_union, codisjoint_iff.mp hcompl.snd.codisjoint, Set.top_eq_univ,
        Set.image_univ]
      calc
        Set.range (Hom.fst f) ⊆ closure (Set.range (Hom.fst f)) := subset_closure
        _ ⊆ interior (Set.range X.map) := hU
        _ ⊆ Set.range X.map := interior_subset
    have h₁ : Disjoint (Set.range (Hom.fst f)) (Hom.fst g '' Set.range V.map) := by
      rw [Set.disjoint_iff, ← Set.disjoint_iff_inter_eq_empty.mp hcompl.fst.disjoint]
      grind
    simp [Disjoint.subset_left_of_subset_union h₀ h₁]
  apply isIso_of_bijective_of_isOpenMap _
    ⟨U.prop.injective, surjective_U⟩
  apply Topology.IsInducing.isOpenMap U.prop.isInducing
  simp [Function.Surjective.range_eq surjective_U]

end TopPair

open HomologyPretheory

variable {C : Type v} [Category C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
  (HP HP' : HomologyPretheory.{u} C c) (i : ι)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
class IsHomotopyInvariant where
  homotopy ⦃X Y : TopPair⦄ (f g : X ⟶ Y) (hfg : Homotopic f g) :
      ∀ (i : ι), (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

namespace IsHomotopyInvariant

open Homotopic

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsHomotopyInvariant where
  of_iso {HP HP'} e hHP := ⟨by
    intro _ _ _ _ hfg _
    have := hHP.homotopy _ _ hfg
    apply ((((HomologyPretheory.forgetₚ _).mapIso e).app _).cancel_iso_hom_left
      ((HP'.Hₚ _).map _) ((HP'.Hₚ _).map _)).mp
    simp only [CategoryTheory.Iso.app_hom, HomologyPretheory.forgetₚ_obj, Functor.mapIso_hom,
      forgetₚ_map, ← (e.hom.homₚ _).naturality]
    cat_disch⟩

variable [IsHomotopyInvariant HP]

def Hₚ : TopPairHomotopyCat.{u} ⥤ C := CategoryTheory.Quotient.lift TopPair.Homotopic.homRel
  (HP.Hₚ i) <| fun _ _ _ _ h ↦ IsHomotopyInvariant.homotopy _ _ h _

lemma quotient_Hₚ_eq : Quotient.functor _ ⋙ (Hₚ HP i) = HP.Hₚ i := Quotient.lift_spec _ _ _

def hₚIsoOfHomotopyEquiv (X Y : TopPair.{u}) (e : X ≃ₕ Y) : (HP.Hₚ i).obj X ≅ (HP.Hₚ i).obj Y :=
  Functor.mapIso (Hₚ HP i) e

def H : TopHomotopyCat.{u} ⥤ C := CategoryTheory.Quotient.lift TopCat.Homotopic.homRel (HP.H i) sorry

lemma quotient_H_eq : Quotient.functor _ ⋙ (H HP i) = HP.H i := Quotient.lift_spec _ _ _

def hIsoOfHomotopyEquiv (X Y : TopCat.{u}) (e : X ≃ₕ Y) : (HP.H i).obj X ≅ (HP.H i).obj Y :=
  Functor.mapIso (H HP i) e

abbrev hZeroToCoeffGroup [Zero ι] (HP : HomologyPretheory C c) (X : TopCat.{u}) :
    (HP.H 0).obj X ⟶ HP.coeffGroup := hToHPUnit _ _ _

instance [Zero ι] (HP : HomologyPretheory C c) (X : TopCat.{u}) [ContractibleSpace X] :
    IsIso (hZeroToCoeffGroup HP X) := sorry

end IsHomotopyInvariant

set_option linter.unusedVariables false in
/-- A `HomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice subspace
`U` from a space `X` yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
class HasExcisionIso where
  [excision ⦃X U V : TopPair⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) (i : ι) :
      IsIso ((HP.Hₚ i).map g)]

attribute [instance] HasExcisionIso.excision

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasExcisionIso where
  of_iso e hHP := { excision _ _ _ _ _ hf hg hcompl hU _ := (NatIso.isIso_map_iff
    ((HomologyPretheory.forgetₚ _).mapIso e) _).mp (hHP.excision _ _ hf hg hcompl hU _) }

/-- A `HomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  [additive (J : Type u) (i : ι) : PreservesColimitsOfShape (Discrete J) (HP.H i)]

attribute [instance] IsAdditive.additive

instance IsAdditive.additive_of_small [IsAdditive HP] (J : Type*) [Small.{u} J] (i : ι) :
    PreservesColimitsOfShape (Discrete J) (HP.H i) :=
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink _).symm) _

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsAdditive where
  of_iso {HP HP'} e _ := { additive _ _ := preservesColimitsOfShape_of_natIso ((HP.iso _) ≪≫
    Functor.isoWhiskerLeft incl ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫ (HP'.iso _).symm) }

section HasPairSequence

variable (i j : ι)

/-- This imposes that a `HomologyPretheory` has the long exact sequence of topological pairs
`⋯ ⟶ H (c.next i) X.fst ⟶ Hₚ (c.next i) X) ⟶ H i X.snd ⟶ H i X.fst ⟶ ⋯`. -/
class HasPairSequence (HP : HomologyPretheory.{u} C c) where
  /-- Exactness of the sequence `H i X.fst ⟶ Hₚ i X ⟶ H j X.snd.` -/
  exact_pair (HP) (X : TopPair) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) ((HP.δ i j).app _)).Exact := by cat_disch
  /-- Exactness of the sequence `Hₚ i X ⟶ H j X.snd ⟶ H j X.fst`. -/
  exact_snd (HP) (X : TopPair) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.δ i j).app _) ((HP.H j).map X.map)).Exact := by cat_disch
  /-- Exactness of the sequence `H i X.snd ⟶ H i X.fst ⟶ Hₚ i X`. -/
  exact_fst (HP) (X : TopPair) (i) :
      (ComposableArrows.mk₂ ((HP.H i).map X.map) ((HP.iso i).hom.app _
      ≫ (HP.Hₚ i).map X.j)).Exact := by cat_disch

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) HasPairSequence where
  of_iso {HP HP'} e hPS := {
    exact_pair X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) ((HP.δ i j).app X)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.Hₚ i).map X.j) ((HP'.δ i j).app X)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((HomologyPretheory.forgetₚ _).mapIso e).app _)
          (((HomologyPretheory.forgetₚ _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (by cat_disch)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, Hom.w_congr_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_pair _ _ _ hij)
    exact_snd X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.H j).map X.map)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.δ i j).app X) ((HP'.H j).map X.map)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((HomologyPretheory.forgetₚ _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, Hom.w_congr_app])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_snd _ _ _ hij)
    exact_fst X i := by
      let pairSeq := ComposableArrows.mk₂ ((HP.H i).map X.map)
        ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.j)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.H i).map X.map)
        ((HP'.iso i).hom.app X.fst ≫ (HP'.Hₚ i).map X.j)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (((HomologyPretheory.forgetₚ _).mapIso e).app _)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map]; simp only [← Category.assoc,
            Hom.iso_comm_congr_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_fst _ _)
  }

variable [HasPairSequence HP]

lemma isZeroHₚDiagOfHasPairSequence (X : TopCat.{u}) : IsZero ((HP.Hₚ i).obj (diag.obj X)) := sorry

namespace TopPair.HomologyPretheory

variable [HasKernels C]

@[simps!]
noncomputable abbrev reducedδ : (HP.Hₚ i) ⟶ proj₂ ⋙ HP.reducedH j where
  app X := kernel.lift (hToHPUnit HP j X.snd) ((HP.δ i j).app _) <| by
    erw [hToHPUnit,
      ← TopPair.Hom.snd_ofHom (Y := diag.obj (TopCat.of PUnit)) (isTerminalPUnit.from X.fst)
        (isTerminalPUnit.from X.snd),
      ← TopPair.proj₂_map (Y := diag.obj (TopCat.of PUnit)) (ofHom (isTerminalPUnit.from X.fst)
        (isTerminalPUnit.from X.snd)),
      ← Functor.comp_map, ← (HP.δ i j).naturality,
      IsZero.eq_zero_of_src (isZeroHₚDiagOfHasPairSequence _ _ _)
        ((HP.δ i j).app (diag.obj (TopCat.of PUnit))),
      HasZeroMorphisms.comp_zero]
    rfl
  naturality X Y f := sorry

noncomputable abbrev reducedδ.app' (X : TopPair) : (HP.Hₚ i).obj X ⟶ (HP.reducedH j).obj X.snd :=  (HP.reducedδ i j).app X

@[simp]
lemma reducedδ_app' (X : TopPair) : reducedδ.app' HP i j X = (HP.reducedδ i j).app X := rfl

class HasReducedPairSequence [instKer : HasKernels C] (HP : HomologyPretheory.{u} C c) where
  /-- Exactness of the sequence `H i X.fst ⟶ Hₚ i X ⟶ H j X.snd.` -/
  exact_pair [instKer] (HP) (X : TopPair) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.Hₚ i).map X.j) (kernel.lift (hToHPUnit HP j X.snd)
        ((HP.δ i j).app _) (sorry))).Exact := by cat_disch
  /-- Exactness of the sequence `Hₚ i X ⟶ H j X.snd ⟶ H j X.fst`. -/
  exact_snd [instKer] (HP) (X : TopPair) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ (kernel.lift (hToHPUnit HP j X.snd) ((HP.δ i j).app _) (sorry))
      ((HP.reducedH j).map X.map)).Exact := by cat_disch
  /-- Exactness of the sequence `H i X.snd ⟶ H i X.fst ⟶ Hₚ i X`. -/
  exact_fst [instKer] (HP) (X : TopPair) (i) :
      (ComposableArrows.mk₂ ((HP.reducedH i).map X.map)
        (kernel.ι (hToHPUnit HP i X.fst) ≫ (HP.iso i).hom.app _ ≫ (HP.Hₚ i).map X.j)).Exact :=
    by cat_disch

instance [HasPairSequence HP] : HasReducedPairSequence HP := sorry

end TopPair.HomologyPretheory

end HasPairSequence

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
class IsExtraordinaryEilenbergSteenrod where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  [homotopy : IsHomotopyInvariant HP]
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  [excision : HasExcisionIso HP]
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves coproducts. -/
  [additive : IsAdditive HP]
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  [exact : HasPairSequence HP]

attribute [instance] IsExtraordinaryEilenbergSteenrod.homotopy IsExtraordinaryEilenbergSteenrod.excision IsExtraordinaryEilenbergSteenrod.additive IsExtraordinaryEilenbergSteenrod.exact

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) IsExtraordinaryEilenbergSteenrod
    where
  of_iso e h := {
    homotopy :=
      IsHomotopyInvariant.instIsClosedUnderIsomorphismsHomologyPretheory.of_iso e h.homotopy
    excision := instIsClosedUnderIsomorphismsHomologyPretheoryHasExcisionIso.of_iso e h.excision
    additive := instIsClosedUnderIsomorphismsHomologyPretheoryIsAdditive.of_iso e h.additive
    exact := instIsClosedUnderIsomorphismsHomologyPretheoryHasPairSequence.of_iso e h.exact
  }

variable (HP HP' : HomologyPretheory.{u} C (ComplexShape.down ℕ))

/-- A `HomologyPretheory` on `ComplexShape.down ℕ` has the dimension axiom if it is trivial on the
terminal space for `n > 0`. -/
class HasDimensionAxiom where
  dimension : ∀ (n : ℕ) [NeZero n], IsZero ((HP.H n).obj (of PUnit)) := by cat_disch

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    HasDimensionAxiom where
  of_iso {HP HP'} e h := ⟨fun n ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl
    ((HomologyPretheory.forgetₚ _).mapIso e) ≪≫ (HP'.iso _).symm).app
    (of PUnit))).mp (h.dimension n)⟩

instance [HasKernels C] [HasDimensionAxiom HP] {n : ℕ} [NeZero n] (X : TopCat.{u}) :
    IsIso ((reducedHToH HP n).app X) := sorry

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends IsExtraordinaryEilenbergSteenrod.{u} HP where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [dimension : HasDimensionAxiom HP]

attribute [instance] IsEilenbergSteenrod.dimension

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C (ComplexShape.down ℕ))
    IsEilenbergSteenrod where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsHomologyPretheoryIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    dimension :=
      instIsClosedUnderIsomorphismsHomologyPretheoryNatDownHasDimensionAxiom.of_iso e h.dimension
  }
