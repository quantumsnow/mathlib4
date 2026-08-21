/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Order.PUnit
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Sigma.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Categories of vector bundles

This bundles the data of vector bundles into various categories. We provide four categories:

* `FixedBaseFixedFiberVectorBundleCat`: the category of vector bundles over a fixed base with fixed
  fiber
* `FixedBaseVectorBundleCat`: the category of vector bundles over a fixed base
* `FGFixedBaseVectorBundleCat`: the category of finite-rank vector bundles over a fixed base
* `VectorBundleCat`: the category of all vector bundles

We also provide an addition on `FixedBaseVectorBundleCat` and `FGFixedBaseVectorBundleCat` via the
Whitney-sum which becomes an additive commutative monoid on their skeleta. Finally, we give
pullbacks as maps between such categories for different bases as well as on their skeleta.

Most significant gaps/`sorry`s:
* Commutative monoid structure of the skeleta
* The pullback is a monoid morphism on the skeleta
-/

@[expose] public section

open Bundle VectorBundle CategoryTheory
universe f r b

variable (R : Type r) [NontriviallyNormedField R] (B : Type b) [TopologicalSpace B] (F : Type f)
  [NormedAddCommGroup F] [NormedSpace R F]

/-- The category of topological vector bundles with fiber prototype `F` over base `B`. -/
structure FixedBaseFixedFiberVectorBundleCat where
  /-- The bundled fibers of an object of `FixedBaseFixedFiberVectorBundleCat`. -/
  E : B → Type f
  [isTopologicalSpaceTotalSpace : TopologicalSpace (TotalSpace F E)]
  [isTopologicalSpaceFibers : (x : B) → TopologicalSpace (E x)]
  [isFiberBundle : FiberBundle F E]
  [isAddCommMonoidFibers : (x : B) → AddCommMonoid (E x)]
  [isModuleFibers : (x : B) → Module R (E x)]
  [isVectorBundle : VectorBundle R F E]

attribute [instance] FixedBaseFixedFiberVectorBundleCat.isTopologicalSpaceTotalSpace
  FixedBaseFixedFiberVectorBundleCat.isTopologicalSpaceFibers
  FixedBaseFixedFiberVectorBundleCat.isFiberBundle
  FixedBaseFixedFiberVectorBundleCat.isAddCommMonoidFibers
  FixedBaseFixedFiberVectorBundleCat.isModuleFibers
  FixedBaseFixedFiberVectorBundleCat.isVectorBundle

instance : Category (FixedBaseFixedFiberVectorBundleCat R B F) where
  Hom VB VB' := VectorBundle.Hom R VB.E VB'.E
  id _ := {
    homProj := ContinuousMap.id _
    homSnd _ := LinearMap.id
  }
  comp f g := {
    homProj := g.homProj.comp f.homProj
    homSnd x := (g.homSnd (f.homProj x)) ∘ₗ f.homSnd x
  }

section BundledFiber

/-- The category of topological vector bundles over base `B`. Note that this is not the disjoint
union category of `FixedBaseFixedFiberVectorBundleCat`. -/
structure FixedBaseVectorBundleCat where
  /-- The fiber prototype of an object of `FixedBaseVectorBundleCat`. -/
  F : Type f
  [isNormedAddCommGroup : NormedAddCommGroup F]
  [isNormedSpace : NormedSpace R F]
  /-- The bundle with fiber prototype `F` over `B`. -/
  bundle : FixedBaseFixedFiberVectorBundleCat.{f, r, b} R B F

attribute [instance] FixedBaseVectorBundleCat.isNormedAddCommGroup
  FixedBaseVectorBundleCat.isNormedSpace

namespace FixedBaseVectorBundleCat

instance : Category (FixedBaseVectorBundleCat R B) where
  Hom VB VB' := VectorBundle.Hom R VB.bundle.E VB'.bundle.E
  id _ := {
    homProj := ContinuousMap.id _
    homSnd _ := LinearMap.id
  }
  comp f g := {
    homProj := g.homProj.comp f.homProj
    homSnd x := (g.homSnd (f.homProj x)) ∘ₗ f.homSnd x
  }

instance : Zero (FixedBaseVectorBundleCat R B) where
  zero := ⟨PUnit, ⟨Bundle.Trivial _ PUnit⟩⟩

noncomputable instance : Add (FixedBaseVectorBundleCat.{f} R B) where
  add VB VB' := ⟨VB.F × VB'.F, ⟨VB.bundle.E ×ᵇ VB'.bundle.E⟩⟩

noncomputable instance : AddCommMonoid (Skeleton (FixedBaseVectorBundleCat R B)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry

/-- The pullback of vector bundles as a map on `FixedBaseVectorBundleCat`. -/
noncomputable def pullback
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) :
    FixedBaseVectorBundleCat R B → FixedBaseVectorBundleCat R B' :=
  fun VB ↦ ⟨VB.F, ⟨f *ᵖ VB.bundle.E⟩⟩

/-- The pullback of vector bundles as a map on the skeleta of `FixedBaseVectorBundleCat`. -/
noncomputable def pullbackSkeleton
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) :
    Skeleton (FixedBaseVectorBundleCat R B) →+ Skeleton (FixedBaseVectorBundleCat R B') where
  toFun VB := (Quotient.lift (Quotient.mk _ ∘ (pullback R f)) (by
    intro VB VB' h
    simp [HasEquiv.Equiv, instHasEquivOfSetoid] at h
    apply Quotient.ind
    sorry) VB)
  map_zero' := sorry
  map_add' := sorry

end FixedBaseVectorBundleCat

/-- The `ObjectProperty` on `FixedBaseVectorBundleCat` of being finitely-generated (i.e. a
finite-rank vector bundle). -/
abbrev FixedBaseVectorBundleCat.isFG : ObjectProperty (FixedBaseVectorBundleCat R B) :=
  fun VB ↦ Module.Finite R VB.F

/-- The category of finite-rank topological vector bundles over `B`. -/
abbrev FGFixedBaseVectorBundleCat := (FixedBaseVectorBundleCat.isFG.{r, b, r} R B).FullSubcategory

namespace FixedBaseFGVectorBundleCat

instance : Zero (FGFixedBaseVectorBundleCat R B) where
  zero := ⟨0, Module.Finite.instPUnit⟩

noncomputable instance : Add (FGFixedBaseVectorBundleCat R B) where
  add VB VB' := ⟨VB.obj + VB'.obj, by
    simp only [FixedBaseVectorBundleCat.isFG, HAdd.hAdd, Add.add]
    have := VB.property
    have := VB'.property
    infer_instance⟩

noncomputable instance : AddCommMonoid (Skeleton (FGFixedBaseVectorBundleCat R B)) where
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  nsmul := nsmulRec
  add_comm := sorry

/-- The pullback of vector bundles as a map on the `FixedBaseFGVectorBundleCat`. -/
noncomputable def pullback
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) :
    FGFixedBaseVectorBundleCat R B → FGFixedBaseVectorBundleCat R B' :=
  fun VB ↦ ⟨FixedBaseVectorBundleCat.pullback R f VB.obj, VB.property⟩

/-- The pullback of vector bundles as a monoid map on the skeleta of
`FixedBaseFGVectorBundleCat`. -/
noncomputable def pullbackSkeleton
    {B B' : Type*} [TopologicalSpace B] [TopologicalSpace B'] (f : C(B', B)) :
    Skeleton (FGFixedBaseVectorBundleCat R B) →+ Skeleton (FGFixedBaseVectorBundleCat R B') where
  toFun VB := (Quotient.lift (Quotient.mk _ ∘ (pullback R f)) sorry VB)
  map_zero' := by cat_disch
  map_add' := by cat_disch

end FixedBaseFGVectorBundleCat

section BundledBase

/-- The category of topological vector bundles. -/
@[nolint checkUnivs, pp_with_univ]
structure VectorBundleCat where
  /-- The base of a topological vector bundle. -/
  B : Type b
  [instTopologicalSpace : TopologicalSpace B]
  /-- The bundle over `B` of a topological vector bundle -/
  bundle : FixedBaseVectorBundleCat.{f} R B

attribute [instance] VectorBundleCat.instTopologicalSpace

namespace VectorBundleCat

instance : Category (VectorBundleCat R) where
  Hom VB VB' := VectorBundle.Hom R VB.bundle.bundle.E VB'.bundle.bundle.E
  id _ := {
    homProj := ContinuousMap.id _
    homSnd _ := LinearMap.id
  }
  comp f g := {
    homProj := g.homProj.comp f.homProj
    homSnd x := (g.homSnd (f.homProj x)) ∘ₗ f.homSnd x
  }

end VectorBundleCat

end BundledBase

end BundledFiber
