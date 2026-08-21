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
public import Mathlib.Topology.Category.TopPair.Basic
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

Most significant gaps/`sorry`s:
* `hIsoReducedHBiprod`: construct the isomorphism `H i X ≅ reducedH i X ⊞ H i ∗`
* If `X` is contractible, the induced map `H 0 X ⟶ H 0 ∗` is an isomorphism.
* `isZeroHₚDiagOfHasPairSequence`: if a (co)homology theory has an exact pair sequence, `H m (X, X)` is
  trivial
* `has_reduced_pair_sequence_exact_fst`: exactness of the long exact sequence in reduced homology
* For a homology theory with the dimension axiom and `m ≠ 0`, the inclusion `reducedH m X → H m X`
  is an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits TopPair TopCat ObjectProperty Opposite

universe u

namespace TopPair

/-- A `HomologyPretheory` is the data of an Eilenberg-Steenrod homology theory. -/
@[ext]
structure HomologyPretheory
    (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  /-- The relative homology functor of a `HomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u} ⥤ C
  /-- The regular homology functor of a `HomologyPretheory`. -/
  H (i : ι) : TopCat.{u} ⥤ C
  /-- `Hₚ` and `H` agree on `TopCat`. -/
  iso (i : ι) : H i ≅ incl ⋙ Hₚ i
  /-- The boundary natural transformation of a `HomologyPretheory`. -/
  δ (i j : ι) : Hₚ i ⟶ proj₂ ⋙ H j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace HomologyPretheory

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι} (i : ι)

/-- A morphism in the category `HomologyPretheory`. -/
@[ext]
structure Hom (HP HP' : HomologyPretheory.{u} C c) where
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

@[simps]
instance : Category (HomologyPretheory.{u} C c) where
  Hom := HomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _ }

variable {HP HP' : HomologyPretheory.{u} C c}

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) = (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}) :
    (HP.δ i j).app X ≫ (f.hom j).app X.left = (f.homₚ i).app X ≫ (HP'.δ i j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (ofTopCat X) ≫ (HP'.iso i).inv.app X = (f.hom i).app X :=
  congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}) :
    (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X = (f.homₚ i).app (ofTopCat X) :=
  congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `HomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
def hₚFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopPair.{u} ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hₚFunctor i).map f))

/-- The forgetful functor that sends a `HomologyPretheory` to its homology functor `H`. -/
@[simps]
def hFunctor (i : ι) : HomologyPretheory.{u} C c ⥤ TopCat.{u} ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((HomologyPretheory.hFunctor i).map f))

/-- The coefficient object of a homology theory is `H 0 ∗`. -/
abbrev coeffObj [Zero ι] (HP : HomologyPretheory C c) := (HP.H 0).obj (TopCat.of PUnit)

section ReducedHomology

variable (HP) [HasKernels C] (i j : ι) (X : TopCat.{u})

/-- The induced map `H i X ⟶ H i ∗`. -/
abbrev hToHPUnit : (HP.H i).obj X ⟶ (HP.H i).obj (TopCat.of PUnit) :=
  (HP.H i).map (TopCat.isTerminalPUnit.from X)

/-- Reduced homology is the kernel of the induced map `H i X ⟶ H i ∗` in unreduced homology. -/
@[simps]
noncomputable def reducedH : TopCat.{u} ⥤ C where
  obj X := kernel (hToHPUnit HP i X)
  map {X Y} f := kernel.lift (hToHPUnit HP i Y) (kernel.ι (hToHPUnit HP i X) ≫ (HP.H i).map f) <| by
      have : (HP.H i).map f ≫ hToHPUnit HP i Y = hToHPUnit HP i X := by
        rw [← Functor.map_comp]
        cat_disch
      cat_disch

/-- The canonical inclusion of reduced homology into unreduced homology. -/
noncomputable def reducedHToH : HP.reducedH i ⟶ HP.H i where
  app X := kernel.ι _
  naturality := sorry

/-- The isomorphism `H i X ≅ reducedH i X ⊞ H i ∗` -/
def hIsoReducedHBiprod [HasBinaryBiproducts C] :
    (HP.H i).obj X ≅ (HP.reducedH i).obj X ⊞ (HP.H i).obj (TopCat.of PUnit) := sorry

end ReducedHomology

variable (HP HP' : HomologyPretheory.{u} C c) (i : ι)

/-- A `HomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps to
the same map in homology -/
class IsHomotopyInvariant (HP : HomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}} {f g : X ⟶ Y} (F : Homotopy f g) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`. -/
abbrev isHomotopyInvariant : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

@[simp]
lemma isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl

instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

namespace IsHomotopyInvariant

open Homotopic

variable [IsHomotopyInvariant HP]

/-- If a `HomologyPretheory` is homotopy-invariant, it induces a functor from the homotopy category
of `TopPair`. -/
def homotopyHₚ : TopPairHomotopyCat.{u} ⥤ C := CategoryTheory.Quotient.lift TopPair.Homotopic.homRel
  (HP.Hₚ i) <| fun _ _ _ _ h ↦ HP.map_eq_of_homotopy h.some _

lemma quotient_Hₚ_eq : Quotient.functor _ ⋙ (homotopyHₚ HP i) = HP.Hₚ i :=
  Quotient.lift_spec _ _ _

/-- If a `HomologyPretheory` is homotopy invariant, it maps homotopy equivalences to isomorphisms.
-/
def hₚIsoOfHomotopyEquiv {X Y : TopPair.{u}} (e : X ≃ₕ Y) : (HP.Hₚ i).obj X ≅ (HP.Hₚ i).obj Y :=
  (homotopyHₚ HP i).mapIso e

/-- For a homotopy-invariant `HomologyPretheory`, this is the induced homology functor on the
homotopy category. -/
def H : TopHomotopyCat.{u} ⥤ C :=
  CategoryTheory.Quotient.lift TopCat.Homotopic.homRel (HP.H i) sorry

lemma quotient_H_eq : Quotient.functor _ ⋙ (H HP i) = HP.H i := Quotient.lift_spec _ _ _

/-- A homotopy-invariant `HomologyPretheory` maps a homotopy equivalence to an isomorphism. -/
def hIsoOfHomotopyEquiv (X Y : TopCat.{u}) (e : X ≃ₕ Y) : (HP.H i).obj X ≅ (HP.H i).obj Y :=
  Functor.mapIso (H HP i) e

/-- If `X` is contractible, the induced map `H 0 X ⟶ H 0 ∗` is an isomorphism. -/
instance [Zero ι] (HP : HomologyPretheory C c) (X : TopCat.{u}) [ContractibleSpace X] :
    IsIso (HP.hToHPUnit 0 X) := sorry

end IsHomotopyInvariant

set_option linter.unusedVariables false in
/-- A `HomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice subspace
`U` from a space `X` yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
class HasExcisionIso where
  [isIso_of_closure_interior_of_isCompl ⦃X U V : TopPair.{u}⦄ (f : U ⟶ X) (g : V ⟶ X)
      (hf : IsEmbedding f) (hg : IsEmbedding g) (hcompl : TopPair.IsCompl f g)
      (hU : closure (Set.range (Hom.fst f)) ⊆ interior (Set.range X.map)) (i : ι) :
      IsIso ((HP.Hₚ i).map g)]

export HasExcisionIso (isIso_of_closure_interior_of_isCompl)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.HasExcisionIso` as `ObjectProperty`. -/
abbrev hasExcisionIso : ObjectProperty (HomologyPretheory.{u} C c) :=
  HasExcisionIso

@[simp]
lemma hasExcisionIso_iff : hasExcisionIso C c HP ↔ HP.HasExcisionIso := .rfl

instance : IsClosedUnderIsomorphisms (hasExcisionIso.{u} C c) where
  of_iso e hHP := { isIso_of_closure_interior_of_isCompl _ _ _ _ _ hf hg hcompl hU _ :=
    (NatIso.isIso_map_iff ((hₚFunctor _).mapIso e) _).mp (hHP.isIso_of_closure_interior_of_isCompl _
      _ hf hg hcompl hU _) }

set_option backward.isDefEq.respectTransparency false in
/-- Under the assumptions of excision, the map of the pair `U` is an isomorphism. -/
lemma isIso_of_isCompl_closure ⦃X U V : TopPair.{u}⦄ (f : U ⟶ X) (g : V ⟶ X) (hf : IsEmbedding f)
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

/-- A `HomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  [preserves_coproducts_u (J : Type u) (i : ι) :
      PreservesColimitsOfShape (Discrete J) (HP.H i)]

attribute [instance] IsAdditive.preserves_coproducts_u

export IsAdditive (preserves_coproducts_u)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsAdditive` as `ObjectProperty`. -/
abbrev isAdditive : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsAdditive

@[simp]
lemma isAdditive_iff : isAdditive C c HP ↔ HP.IsAdditive := .rfl

instance IsAdditive.preserves_coproducts_of_small
    [HP.IsAdditive] (J : Type*) [Small.{u} J] (i : ι) :
      PreservesColimitsOfShape (Discrete J) (HP.H i) :=
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink _).symm) _

instance : IsClosedUnderIsomorphisms (isAdditive.{u} C c) where
  of_iso {HP HP'} e _ := { preserves_coproducts_u _ _ :=
    preservesColimitsOfShape_of_natIso ((HP.iso _) ≪≫
      Functor.isoWhiskerLeft incl ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm) }

section HasPairSequence

variable (i j : ι)

/-- This imposes that a `HomologyPretheory` has the long exact sequence of topological pairs
`⋯ ⟶ H (c.next i) X.fst ⟶ Hₚ (c.next i) X) ⟶ H i X.snd ⟶ H i X.fst ⟶ ⋯`. -/
class HasPairSequence (HP : HomologyPretheory.{u} C c) where
  /-- Exactness of the sequence `H i X.fst ⟶ Hₚ i X ⟶ H j X.snd.` -/
  exact_pair (HP) (X : TopPair.{u}) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.Hₚ i).map X.inclFst) ((HP.δ i j).app _)).Exact := by cat_disch
  /-- Exactness of the sequence `Hₚ i X ⟶ H j X.snd ⟶ H j X.fst`. -/
  exact_snd (HP) (X : TopPair.{u}) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.δ i j).app _) ((HP.H j).map X.map)).Exact := by cat_disch
  /-- Exactness of the sequence `H i X.snd ⟶ H i X.fst ⟶ Hₚ i X`. -/
  exact_fst (HP) (X : TopPair.{u}) (i) :
      (ComposableArrows.mk₂ ((HP.H i).map X.map) ((HP.iso i).hom.app _
      ≫ (HP.Hₚ i).map X.inclFst)).Exact := by cat_disch

export HasPairSequence (exact_pair exact_snd exact_fst)

variable (C c) in
/-- An abbreviation for `HomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev hasPairSequence : ObjectProperty (HomologyPretheory.{u} C c) :=
  HasPairSequence

@[simp]
lemma hasPairSequence_iff : hasPairSequence C c HP ↔ HP.HasPairSequence := .rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (hasPairSequence.{u} C c) where
  of_iso {HP HP'} e hPS := {
    exact_pair X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.Hₚ i).map X.inclFst) ((HP.δ i j).app X)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.Hₚ i).map X.inclFst) ((HP'.δ i j).app X)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((hₚFunctor _).mapIso e).app _)
          (((hₚFunctor _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (by cat_disch)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, -Functor.isoWhiskerLeft_trans,
            Hom.w_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_pair _ _ _ hij)
    exact_snd X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.H j).map X.map)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.δ i j).app X) ((HP'.H j).map X.map)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((hₚFunctor _).mapIso e).app _)
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (by simp [pairSeq, pairSeq', -Functor.isoWhiskerLeft_trans, Hom.w_app])
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            erw [iso_homₚ_inv_hom_app]
            simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_snd _ _ _ hij)
    exact_fst X i := by
      let pairSeq := ComposableArrows.mk₂ ((HP.H i).map X.map)
        ((HP.iso i).hom.app X.fst ≫ (HP.Hₚ i).map X.inclFst)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.H i).map X.map)
        ((HP'.iso i).hom.app X.fst ≫ (HP'.Hₚ i).map X.inclFst)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((proj₂.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((HP.iso _) ≪≫ incl.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          (((hₚFunctor _).mapIso e).app _)
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            erw [iso_homₚ_inv_hom_app]
            simp [pairSeq, pairSeq'])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, hₚFunctor])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_fst _ _)
  }

variable [HasPairSequence HP]

lemma isZeroHₚDiagOfHasPairSequence (X : TopCat.{u}) : IsZero ((HP.Hₚ i).obj (diag.obj X)) := sorry

section Reduced

variable [HasKernels C]

/-- The boundary map in reduced homology. -/
@[simps!]
noncomputable def reducedδ : (HP.Hₚ i) ⟶ proj₂ ⋙ HP.reducedH j where
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

lemma has_reduced_pair_sequence_exact_pair
      (X : TopPair) (i j) (hij : c.Rel i j) :
    (ComposableArrows.mk₂ ((HP.Hₚ i).map X.inclFst) (kernel.lift (hToHPUnit HP j X.snd)
      ((HP.δ i j).app _) sorry)).Exact := by cat_disch

lemma has_reduced_pair_sequence_exact_snd
      (X : TopPair) (i j) (hij : c.Rel i j) :
    (ComposableArrows.mk₂ (kernel.lift (hToHPUnit HP j X.snd) ((HP.δ i j).app _) sorry)
      ((HP.reducedH j).map X.map)).Exact := by cat_disch

lemma has_reduced_pair_sequence_exact_fst
      (X : TopPair) (i) :
    (ComposableArrows.mk₂ ((HP.reducedH i).map X.map) (kernel.ι (hToHPUnit HP i X.fst) ≫
      (HP.iso i).hom.app _ ≫ (HP.Hₚ i).map X.inclFst)).Exact := sorry

end Reduced

end HasPairSequence

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
class IsExtraordinaryEilenbergSteenrod where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  [isHomotopyInvariant : HP.IsHomotopyInvariant]
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  [hasExcisionIso : HP.HasExcisionIso]
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves coproducts. -/
  [isAdditive : HP.IsAdditive]
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  [hasPairSequence : HP.HasPairSequence]

attribute [instance] IsExtraordinaryEilenbergSteenrod.isHomotopyInvariant
  IsExtraordinaryEilenbergSteenrod.hasExcisionIso
  IsExtraordinaryEilenbergSteenrod.isAdditive
  IsExtraordinaryEilenbergSteenrod.hasPairSequence

variable (C c) in
/-- An abbreviation for `HomologyPretheory.IsExtraordinaryEilenbergSteenrod` as `ObjectProperty`. -/
abbrev isExtraordinaryEilenbergSteenrod : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsExtraordinaryEilenbergSteenrod

@[simp]
lemma isExtraordinaryEilenbergSteenrod_iff :
    isExtraordinaryEilenbergSteenrod C c HP ↔ HP.IsExtraordinaryEilenbergSteenrod := .rfl

instance : IsClosedUnderIsomorphisms (isExtraordinaryEilenbergSteenrod C c)
    where
  of_iso e h := {
    isHomotopyInvariant :=
      instIsClosedUnderIsomorphismsIsHomotopyInvariant.of_iso e h.isHomotopyInvariant
    hasExcisionIso := instIsClosedUnderIsomorphismsHasExcisionIso.of_iso e h.hasExcisionIso
    isAdditive := instIsClosedUnderIsomorphismsIsAdditive.of_iso e h.isAdditive
    hasPairSequence := instIsClosedUnderIsomorphismsHasPairSequence.of_iso e h.hasPairSequence
  }

variable [Zero ι] (HP HP' : HomologyPretheory.{u} C c)

/-- A `HomologyPretheory` has the dimension axiom if it is trivial on the
terminal space for `i ≠ 0`. -/
class HasDimensionAxiom where
  isZero_PUnit_of_NeZero : ∀ (i : ι) [NeZero i], IsZero ((HP.H i).obj (TopCat.of PUnit)) :=
    by cat_disch

export HasDimensionAxiom (isZero_PUnit_of_NeZero)

variable (C) in
/-- An abbreviation for `HomologyPretheory.HasDimensionAxiom` as `ObjectProperty`. -/
abbrev hasDimensionAxiom : ObjectProperty (HomologyPretheory.{u} C c) :=
  HasDimensionAxiom

@[simp]
lemma hasDimensionAxiom_iff : hasDimensionAxiom C HP ↔ HP.HasDimensionAxiom := .rfl

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) (hasDimensionAxiom.{u} C) where
  of_iso {HP HP'} e h := ⟨fun n ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl
    ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm).app
    (TopCat.of PUnit))).mp (h.isZero_PUnit_of_NeZero n)⟩

instance [HasKernels C] [HasDimensionAxiom HP] {i : ι} [NeZero i] (X : TopCat.{u}) :
    IsIso ((reducedHToH HP i).app X) := sorry

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends HP.IsExtraordinaryEilenbergSteenrod.{u} where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [hasDimensionAxiom : HP.HasDimensionAxiom]

attribute [instance] IsEilenbergSteenrod.hasDimensionAxiom

variable (C) in
/-- An abbreviation for `HomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev isEilenbergSteenrod : ObjectProperty (HomologyPretheory.{u} C c) :=
  IsEilenbergSteenrod

@[simp]
lemma isEilenbergSteenrod_iff : isEilenbergSteenrod C HP ↔ HP.IsEilenbergSteenrod := .rfl

instance : IsClosedUnderIsomorphisms (C := HomologyPretheory C c) (isEilenbergSteenrod.{u} C) where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    hasDimensionAxiom :=
      instIsClosedUnderIsomorphismsHasDimensionAxiom.of_iso e h.hasDimensionAxiom
  }

end HomologyPretheory

-- TODO: make this the dual of `HomologyPretheory`. At this time, `to_dual` does not support
-- dualizing `TopPair.{u}ᵒᵖ ⥤ C` to `TopPair.{u} ⥤ C`.
/-- A `CohomologyPretheory` is the data of an Eilenberg-Steenrod cohomology theory. -/
structure CohomologyPretheory
    (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι) where
  mkₚ ::
  /-- The relative homology functor of a `CohomologyPretheory`. -/
  Hₚ (i : ι) : TopPair.{u}ᵒᵖ ⥤ C
  /-- The regular homology functor of a `CohomologyPretheory`. -/
  H (i : ι) : TopCat.{u}ᵒᵖ ⥤ C
  /-- `Hₚ` and `H` agree on `TopCatᵒᵖ`. -/
  iso (i : ι) : H i ≅ incl.op ⋙ Hₚ i
  /-- The boundary natural transformation of a `CohomologyPretheory`. -/
  δ (i j : ι) : proj₂.op ⋙ H i ⟶ Hₚ j
  /-- The boundary map is only nonzero if `c.Rel i j`. -/
  shape_δ (i j : ι) (h : ¬ c.Rel i j) : δ i j = 0 := by cat_disch

namespace CohomologyPretheory

/-- A morphism in the category `CohomologyPretheory`. -/
@[ext]
structure Hom {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    (HP HP' : CohomologyPretheory.{u} C c) where
  /-- The natural transformation of relative homology functors in a morphism of
  `CohomologyPretheory`s. -/
  homₚ (i : ι) : HP.Hₚ i ⟶ HP'.Hₚ i
  /-- The natural transformation of homology functors in a morphism of
  `CohomologyPretheory`s. -/
  hom (i : ι) : HP.H i ⟶ HP'.H i := (HP.iso i).hom ≫ incl.op.whiskerLeft (homₚ i) ≫ (HP'.iso i).inv
  /-- `homₚ` and `hom` need to be compatible with `CohomologyPretheory.iso`. -/
  iso_comm (i : ι) :
    (HP.iso i).hom ≫ incl.op.whiskerLeft (homₚ i) = hom i ≫ (HP'.iso i).hom := by cat_disch
  /-- `homₚ` needs to be compatible with the boundary maps. -/
  w (i j : ι) : proj₂.op.whiskerLeft (hom i) ≫ HP'.δ i j = HP.δ i j ≫ homₚ j := by cat_disch

attribute [reassoc (attr := simp)] CohomologyPretheory.Hom.iso_comm
attribute [reassoc (attr := local simp)] CohomologyPretheory.Hom.w

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι} (i : ι)

@[simps]
instance : Category (CohomologyPretheory.{u} C c) where
  Hom := CohomologyPretheory.Hom
  id _ := { homₚ _ := 𝟙 _ }
  comp f g := { homₚ _ := f.homₚ _ ≫ g.homₚ _, w := sorry }

variable {HP HP' : CohomologyPretheory.{u} C c}

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.iso_comm_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}ᵒᵖ) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (op (ofTopCat X.unop)) =
      (f.hom i).app X ≫ (HP'.iso i).hom.app X :=
  congr($(f.iso_comm _).app _)

@[reassoc]
lemma Hom.iso_comm' (f : HP ⟶ HP') (i : ι) :
  incl.op.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = (HP.iso i).inv ≫ f.hom i := sorry

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.iso_comm_app' (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}ᵒᵖ) :
  (f.homₚ i).app (op (ofTopCat X.unop)) ≫ (HP'.iso i).inv.app X =
    (HP.iso i).inv.app X ≫ (f.hom i).app X := congr($(f.iso_comm' _).app _)

-- TODO: generate this with `@[to_app]`
@[reassoc]
lemma Hom.w_app (f : HP ⟶ HP') (i j : ι) (X : TopPair.{u}ᵒᵖ) :
    (f.hom i).app (op X.unop.snd) ≫ (HP'.δ i j).app X = (HP.δ i j).app X ≫ (f.homₚ j).app X :=
  congr($(f.w _ _).app _)

@[reassoc]
lemma iso_homₚ_inv_hom (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).hom ≫ incl.op.whiskerLeft (f.homₚ i) ≫ (HP'.iso i).inv = f.hom i := by simp

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma iso_homₚ_inv_hom_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}ᵒᵖ) :
    (HP.iso i).hom.app X ≫ (f.homₚ i).app (op (ofTopCat X.unop)) ≫ (HP'.iso i).inv.app X =
      (f.hom i).app X :=
  congr($(iso_homₚ_inv_hom _ _).app _)

@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ (f : HP ⟶ HP') (i : ι) :
    (HP.iso i).inv ≫ f.hom i ≫ (HP'.iso i).hom = incl.op.whiskerLeft (f.homₚ i) :=
  ((Iso.inv_comp_eq (HP.iso i)).mpr (f.iso_comm i).symm)

-- TODO: generate this with `@[to_app]`
@[reassoc (attr := simp)]
lemma inv_hom_iso_homₚ_app (f : HP ⟶ HP') (i : ι) (X : TopCat.{u}ᵒᵖ) :
    (HP.iso i).inv.app X ≫ (f.hom i).app X ≫ (HP'.iso i).hom.app X =
      (f.homₚ i).app (op (ofTopCat X.unop)) :=
  congr($(inv_hom_iso_homₚ _ _).app _)

/-- The forgetful functor that sends a `CohomologyPretheory` to it's relative homology functor `Hₚ`.
-/
@[simps]
def hₚFunctor (i : ι) : CohomologyPretheory.{u} C c ⥤ TopPair.{u}ᵒᵖ ⥤ C where
  obj HP := HP.Hₚ i
  map f := f.homₚ i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.homₚ i) :=
  inferInstanceAs (IsIso ((CohomologyPretheory.hₚFunctor i).map f))

/-- The forgetful functor that sends a `CohomologyPretheory` to its homology functor `H`. -/
@[simps]
def hFunctor (i : ι) : CohomologyPretheory.{u} C c ⥤ TopCat.{u}ᵒᵖ ⥤ C where
  obj HP := HP.H i
  map f := f.hom i

instance (f : HP ⟶ HP') [IsIso f] (i : ι) : IsIso (f.hom i) :=
  inferInstanceAs (IsIso ((CohomologyPretheory.hFunctor i).map f))

/-- The coefficient object of a cohomology theory is `H 0 ∗`. -/
abbrev coeffObj [Zero ι] (HP : CohomologyPretheory C c) := (HP.H 0).obj (op (TopCat.of PUnit))

variable (HP HP' : CohomologyPretheory.{u} C c) (i : ι)

/-- A `CohomologyPretheory` is homotopy-invariant if its homology functor `Hₚ` takes homotopic maps
to the same map in homology -/
class IsHomotopyInvariant (HP : CohomologyPretheory.{u} C c) where
  map_eq_of_homotopy (HP) {X Y : TopPair.{u}ᵒᵖ} {f g : X ⟶ Y} (F : Homotopy f.unop g.unop) (i : ι) :
    (HP.Hₚ i).map f = (HP.Hₚ i).map g := by cat_disch

export IsHomotopyInvariant (map_eq_of_homotopy)

variable (C c) in
/-- An abbreviation for `CohomologyPretheory.IsHomotopyInvariant` as `ObjectProperty`. -/
abbrev isHomotopyInvariant : ObjectProperty (CohomologyPretheory.{u} C c) :=
  IsHomotopyInvariant

@[simp]
lemma isHomotopyInvariant_iff : isHomotopyInvariant C c HP ↔ IsHomotopyInvariant HP := .rfl

instance : IsClosedUnderIsomorphisms (isHomotopyInvariant.{u} C c) where
  of_iso e _ := ⟨fun F _ ↦ by
    simp only [← cancel_epi ((e.hom.homₚ _).app _), ← NatTrans.naturality,
      map_eq_of_homotopy _ F _]⟩

set_option linter.unusedVariables false in
/-- A `CohomologyPretheory` has the excision-isomorphism, if cutting out a sufficiently nice
subspace `U` from a space `X` yields an isomorphism `Hₚ i X ≅ Hₚ i (X \ U)`. -/
class HasExcisionIso where
  [isIso_of_closure_interior_of_isCompl ⦃X U V : TopPair.{u}ᵒᵖ⦄ (f : X ⟶ U) (g : X ⟶ V)
      (hf : IsEmbedding f.unop) (hg : IsEmbedding g.unop) (hcompl : TopPair.IsCompl f.unop g.unop)
      (hU : closure (Set.range (Hom.fst f.unop)) ⊆ interior (Set.range X.unop.map)) (i : ι) :
      IsIso ((HP.Hₚ i).map g)]

export HasExcisionIso (isIso_of_closure_interior_of_isCompl)

variable (C c) in
/-- An abbreviation for `CohomologyPretheory.HasExcisionIso` as `ObjectProperty`. -/
abbrev hasExcisionIso : ObjectProperty (CohomologyPretheory.{u} C c) :=
  HasExcisionIso

@[simp]
lemma hasExcisionIso_iff : hasExcisionIso C c HP ↔ HP.HasExcisionIso := .rfl

instance : IsClosedUnderIsomorphisms (hasExcisionIso.{u} C c) where
  of_iso e hHP := { isIso_of_closure_interior_of_isCompl _ _ _ _ _ hf hg hcompl hU _ :=
    (NatIso.isIso_map_iff ((hₚFunctor _).mapIso e) _).mp (hHP.isIso_of_closure_interior_of_isCompl _
      _ hf hg hcompl hU _) }

/-- A `CohomologyPretheory` is additive if its homology functor preserves coproducts. -/
class IsAdditive where
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves colimits. -/
  [preserves_products_u (J : Type u) (i : ι) :
      PreservesLimitsOfShape (Discrete J) (HP.H i)]

attribute [instance] IsAdditive.preserves_products_u

export IsAdditive (preserves_products_u)

variable (C c) in
/-- An abbreviation for `CohomologyPretheory.IsAdditive` as `ObjectProperty`. -/
abbrev isAdditive : ObjectProperty (CohomologyPretheory.{u} C c) :=
  IsAdditive

@[simp]
lemma isAdditive_iff : isAdditive C c HP ↔ HP.IsAdditive := .rfl

instance IsAdditive.preserves_coproducts_of_small
    [HP.IsAdditive] (J : Type*) [Small.{u} J] (i : ι) :
      PreservesLimitsOfShape (Discrete J) (HP.H i) :=
  preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink _).symm) _

instance : IsClosedUnderIsomorphisms (isAdditive.{u} C c) where
  of_iso {HP HP'} e _ := { preserves_products_u _ _ :=
    preservesLimitsOfShape_of_natIso ((HP.iso _) ≪≫
      Functor.isoWhiskerLeft incl.op ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm) }

section HasPairSequence

variable (i j : ι)

set_option backward.isDefEq.respectTransparency false in
/-- This imposes that a `CohomologyPretheory` has the long exact sequence of topological pairs
`⋯ ⟶ H (c.next i) X.fst ⟶ Hₚ (c.next i) X) ⟶ H i X.snd ⟶ H i X.fst ⟶ ⋯`. -/
class HasPairSequence (HP : CohomologyPretheory.{u} C c) where
  exact_pair (HP) (X : TopPair.{u}ᵒᵖ) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.δ i j).app _) ((HP.Hₚ j).map ((inclFst X.unop).op))).Exact :=
    by cat_disch
  exact_snd (HP) (X : TopPair.{u}ᵒᵖ) (i j) (hij : c.Rel i j) :
      (ComposableArrows.mk₂ ((HP.H i).map (X.unop.map.op)) ((HP.δ i j).app X)).Exact := by cat_disch
  exact_fst (HP) (X : TopPair.{u}ᵒᵖ) (i) :
      (ComposableArrows.mk₂ ((HP.Hₚ i).map (X.unop.inclFst.op) ≫ (HP.iso i).inv.app (op X.unop.fst))
        ((HP.H i).map (X.unop.map.op))).Exact := by cat_disch

export HasPairSequence (exact_pair exact_snd exact_fst)

variable (C c) in
/-- An abbreviation for `CohomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev hasPairSequence : ObjectProperty (CohomologyPretheory.{u} C c) :=
  HasPairSequence

@[simp]
lemma hasPairSequence_iff : hasPairSequence C c HP ↔ HP.HasPairSequence := .rfl

set_option backward.isDefEq.respectTransparency false in
instance : IsClosedUnderIsomorphisms (hasPairSequence.{u} C c) where
  of_iso {HP HP'} e hPS := {
    exact_pair X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.δ i j).app X) ((HP.Hₚ j).map X.unop.inclFst.op)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.δ i j).app X) ((HP'.Hₚ j).map X.unop.inclFst.op)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          ((proj₂.op.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.op.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((hₚFunctor _).mapIso e).app _)
          (((hₚFunctor _).mapIso e).app _)
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, -Functor.isoWhiskerLeft_trans,
            Hom.w_app])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map, hₚFunctor])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_pair _ _ _ hij)
    exact_snd X i j hij := by
      let pairSeq := ComposableArrows.mk₂ ((HP.H i).map X.unop.map.op) ((HP.δ i j).app X)
      let pairSeq' := ComposableArrows.mk₂ ((HP'.H i).map X.unop.map.op) ((HP'.δ i j).app X)
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((HP.iso _) ≪≫ incl.op.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          ((proj₂.op.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.op.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (((hₚFunctor _).mapIso e).app _)
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            erw [iso_homₚ_inv_hom_app]
            simp [pairSeq, pairSeq', ComposableArrows.Precomp.map])
          (by simp [pairSeq, pairSeq', ComposableArrows.Precomp.map,-Functor.isoWhiskerLeft_trans,
            Hom.w_app])
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_snd _ _ _ hij)
    exact_fst X i := by
      let pairSeq :=
        ComposableArrows.mk₂ ((HP.Hₚ i).map (X.unop.inclFst.op) ≫
          (HP.iso i).inv.app (op X.unop.fst)) ((HP.H i).map (X.unop.map.op))
      let pairSeq' := ComposableArrows.mk₂
        ((HP'.Hₚ i).map (X.unop.inclFst.op) ≫ (HP'.iso i).inv.app (op X.unop.fst))
        ((HP'.H i).map (X.unop.map.op))
      have pairSeqIso : pairSeq ≅ pairSeq' :=
        ComposableArrows.isoMk₂
          (((hₚFunctor _).mapIso e).app _)
          (((HP.iso _) ≪≫ incl.op.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm).app _)
          ((proj₂.op.isoWhiskerLeft ((HP.iso _) ≪≫
            incl.op.isoWhiskerLeft ((hₚFunctor _).mapIso e) ≪≫
            (HP'.iso _).symm)).app _)
          (by
            simp only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom]
            erw [iso_homₚ_inv_hom_app]
            simp only [pairSeq, pairSeq', Fin.zero_eta, Fin.mk_one,ComposableArrows.precomp_map,
              ComposableArrows.Precomp.map_zero_one, Functor.mapIso_hom, hₚFunctor_map,
              ← Category.assoc, ← ((e.hom.homₚ i).naturality)]
            simp only [Category.assoc, incl, e.hom.iso_comm_app' i (op X.unop.fst)])
          (by
            simp only [pairSeq, pairSeq', ComposableArrows.precomp_map,
              ComposableArrows.Precomp.map, Iso.app_hom, Functor.isoWhiskerLeft_hom]
            simp)
      exact ComposableArrows.exact_of_iso pairSeqIso (hPS.exact_fst _ _)
  }

variable [HasPairSequence HP]

lemma isZeroHₚDiagOfHasPairSequence (X : TopCat.{u}ᵒᵖ) : IsZero ((HP.Hₚ i).obj (diag.op.obj X)) :=
  sorry

end HasPairSequence

/-- An extraordinary Eilenberg-Steenrod homology theory requires the homotopy, excision, additivity,
and exactness axioms. -/
class IsExtraordinaryEilenbergSteenrod where
  /-- Invariance of an extraordinary Eilenberg-Steenrod homology theory on homotopic maps. -/
  [isHomotopyInvariant : HP.IsHomotopyInvariant]
  /-- Excision axiom of an extraordinary Eilenberg-Steenrod homology theory. -/
  [hasExcisionIso : HP.HasExcisionIso]
  /-- An extraordinary Eilenberg-Steenrod homology functor preserves coproducts. -/
  [isAdditive : HP.IsAdditive]
  /-- The long exact sequence of topological pairs in an extraordinary Eilenberg-Steenrod homology
  theory. -/
  [hasPairSequence : HP.HasPairSequence]

attribute [instance] IsExtraordinaryEilenbergSteenrod.isHomotopyInvariant
  IsExtraordinaryEilenbergSteenrod.hasExcisionIso
  IsExtraordinaryEilenbergSteenrod.isAdditive
  IsExtraordinaryEilenbergSteenrod.hasPairSequence

variable (C c) in
/-- An abbreviation for `CohomologyPretheory.IsExtraordinaryEilenbergSteenrod` as `ObjectProperty`.
-/
abbrev isExtraordinaryEilenbergSteenrod : ObjectProperty (CohomologyPretheory.{u} C c) :=
  IsExtraordinaryEilenbergSteenrod

@[simp]
lemma isExtraordinaryEilenbergSteenrod_iff :
    isExtraordinaryEilenbergSteenrod C c HP ↔ HP.IsExtraordinaryEilenbergSteenrod := .rfl

instance : IsClosedUnderIsomorphisms (isExtraordinaryEilenbergSteenrod C c)
    where
  of_iso e h := {
    isHomotopyInvariant :=
      instIsClosedUnderIsomorphismsIsHomotopyInvariant.of_iso e h.isHomotopyInvariant
    hasExcisionIso := instIsClosedUnderIsomorphismsHasExcisionIso.of_iso e h.hasExcisionIso
    isAdditive := instIsClosedUnderIsomorphismsIsAdditive.of_iso e h.isAdditive
    hasPairSequence := instIsClosedUnderIsomorphismsHasPairSequence.of_iso e h.hasPairSequence
  }

variable [Zero ι] (HP HP' : CohomologyPretheory.{u} C c)

/-- A `CohomologyPretheory` has the dimension axiom if it is trivial on the
terminal space for `i ≠ 0`. -/
class HasDimensionAxiom where
  isZero_PUnit_of_NeZero : ∀ (i : ι) [NeZero i], IsZero ((HP.H i).obj (op (TopCat.of PUnit))) :=
    by cat_disch

export HasDimensionAxiom (isZero_PUnit_of_NeZero)

variable (C) in
/-- An abbreviation for `CohomologyPretheory.HasDimensionAxiom` as `ObjectProperty`. -/
abbrev hasDimensionAxiom : ObjectProperty (CohomologyPretheory.{u} C c) :=
  HasDimensionAxiom

@[simp]
lemma hasDimensionAxiom_iff : hasDimensionAxiom C HP ↔ HP.HasDimensionAxiom := .rfl

instance : IsClosedUnderIsomorphisms (C := CohomologyPretheory C c) (hasDimensionAxiom.{u} C) where
  of_iso {HP HP'} e h := ⟨fun n ↦ (Iso.isZero_iff (((HP.iso _) ≪≫ Functor.isoWhiskerLeft incl.op
    ((hₚFunctor _).mapIso e) ≪≫ (HP'.iso _).symm).app
    (op (TopCat.of PUnit)))).mp (h.isZero_PUnit_of_NeZero n)⟩

/-- An Eilenberg-Steenrod homology theory is an extraordinary Eilenberg-Steenrod homology theory
which additionally satisfies the dimension axiom. -/
class IsEilenbergSteenrod extends HP.IsExtraordinaryEilenbergSteenrod.{u} where
  /-- An Eilenberg-Steenrod homology theory is trivial on the terminal space for `n > 0`. -/
  [hasDimensionAxiom : HP.HasDimensionAxiom]

attribute [instance] IsEilenbergSteenrod.hasDimensionAxiom

variable (C) in
/-- An abbreviation for `CohomologyPretheory.HasPairSequence` as `ObjectProperty`. -/
abbrev isEilenbergSteenrod : ObjectProperty (CohomologyPretheory.{u} C c) :=
  IsEilenbergSteenrod

@[simp]
lemma isEilenbergSteenrod_iff : isEilenbergSteenrod C HP ↔ HP.IsEilenbergSteenrod := .rfl

instance :
    IsClosedUnderIsomorphisms (C := CohomologyPretheory C c) (isEilenbergSteenrod.{u} C) where
  of_iso e h := {
    1 := instIsClosedUnderIsomorphismsIsExtraordinaryEilenbergSteenrod.of_iso e h.1
    hasDimensionAxiom :=
      instIsClosedUnderIsomorphismsHasDimensionAxiom.of_iso e h.hasDimensionAxiom
  }

end CohomologyPretheory

end TopPair
#lint
