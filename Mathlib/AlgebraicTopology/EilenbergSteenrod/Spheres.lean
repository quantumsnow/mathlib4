/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.AlgebraicTopology.EilenbergSteenrod

/-!
# Homology of spheres

This file contains a computation of the homology of spheres from the Eilenberg-Steenrod axioms. It
still contains a number of `sorry`s.

The strategy is to compute the 0-homology of `𝕊 0`, from that compute the reduced homology of all
spheres, and finally compute the unreduced homology.

Most significant gaps/`sorry`s:
* `isColimitSphereZero`: show that `𝕊 0` is a coproduct
* show that the map `reducedH m (𝕊 n) ⟶ H m (𝕊 n, 𝔻 n)` (`reducedHSphereToHₚSphereDiskPair`) is an
  iso
* `puncturedSphereDiskPairToSphereDiskPair`: construct this embedding `(𝕊* n, 𝔻* n) ⟶ (𝕊 n, 𝔻 n)`
* `puncturedSphereDiskPairHomotopyEquiv`: construct this homotopy equivalence
  `((𝕊* (n + 1)), (𝔻* (n + 1))) ≃ₕ (𝔻 (n + 1), 𝕊 n)`
* show that the reduced boundary map `H (m + 1) (𝔻 (n + 1), 𝕊 n) ⟶ reducedH m (𝕊 n)`
  (`hₚDiskSpherePairToReducedHSphere`) is an iso
* `isZero_reducedHSphere_of'` and `isZero_reducedHSphere_of''`: show that `reducedH 0 (𝕊 k)` and
  `reducedH k (𝕊 0)` are trivial
* `reducedHSphereToCoeffObj`: construct the map `reducedH 0 (𝕊 0) ⟶ coeffObj` and show that it is an
  isomorphism
-/

@[expose] public section

open CategoryTheory TopCat TopPair Limits HomologyPretheory

namespace EilenbergSteenrod.Spheres

universe u v

variable (HP : HomologyPretheory.{u} Ab.{v} (ComplexShape.down ℕ)) [IsEilenbergSteenrod HP]
  (m n k : ℕ)

/-- The inclusion of 1 into `𝕊 0`. -/
def ptInclSphereZeroPos : of PUnit ⟶ 𝕊 0 :=
  ofHom (ContinuousMap.const _ (ULift.up ⟨!₂[1], sorry⟩))

/-- The inclusion of -1 into `𝕊 0`. -/
def ptInclSphereZeroNeg : of PUnit ⟶ 𝕊 0 :=
  ofHom (ContinuousMap.const _ (ULift.up ⟨!₂[-1], sorry⟩))

/-- The coproduct cofan of `𝕊 0`. -/
noncomputable def sphereZeroCofan := BinaryCofan.mk ptInclSphereZeroPos.{u} ptInclSphereZeroNeg

/-- The coproduct cofan of `𝕊 0` is a colimit. -/
def isColimitSphereZero : IsColimit sphereZeroCofan := sorry

/-- The image of the coproduct cofan of `𝕊 0` under homology. -/
noncomputable def hSphereZeroCocone :
    Cocone (pair (of PUnit) (of PUnit) ⋙ HP.H n) :=
  (HP.H _).mapCocone sphereZeroCofan

/-- The image of the coproduct cofan of `𝕊 0` under homology is a colimit. -/
noncomputable def isColimitHSphereZeroCocone :
    IsColimit (hSphereZeroCocone HP n) :=
  ((IsAdditive.preserves_coproducts_of_small _ _ _).preservesColimit.preserves
    isColimitSphereZero).some

/-- The image of the coproduct cofan of `𝕊 0` under `n`th homology as a cofan on `H n ∗`. -/
noncomputable def hSphereZeroCofan :
    BinaryCofan ((HP.H n).obj (TopCat.of PUnit)) ((HP.H n).obj (TopCat.of PUnit)) :=
  (Cocone.precomposeEquivalence (pairComp (of PUnit) (of PUnit) (HP.H _))).functor.obj
    ((HP.H _).mapCocone sphereZeroCofan)

/-- The image of the coproduct cofan of `𝕊 0` under `n`th homology as a cofan on `H n ∗` is a
colimit. -/
noncomputable def isColimitHZeroSphereZeroCofan :
    IsColimit (hSphereZeroCofan HP n) :=
  IsColimit.equivOfNatIsoOfIso _ _ _ (Iso.refl _) (isColimitHSphereZeroCocone HP n)

/-- The universal map `H n (𝕊 0) ⟶ H n ∗ ⊞ H n ∗` induced by the coproduct
`H 0 (𝕊 0)`. -/
noncomputable def hSphereZeroToHPUnitBiprod :
    (HP.H n).obj (𝕊 0) ⟶ ((HP.H n).obj (TopCat.of PUnit)) ⊞ ((HP.H n).obj (TopCat.of PUnit)) :=
  (isColimitHZeroSphereZeroCofan _ _).desc (BinaryBiproduct.bicone _ _).toCocone

/-- The universal map `H 0 (𝕊 0) ⟶ H n ∗ ⊞ H n ∗` is an isomorphism. -/
instance : IsIso (hSphereZeroToHPUnitBiprod HP n) :=
  (isColimitHZeroSphereZeroCofan _ _).nonempty_isColimit_iff_isIso_desc.mp
    ⟨(BinaryBiproduct.isColimit _ _)⟩

/-- For `n ≠ 0`, `H n (𝕊 0)` is trivial. -/
lemma isZero_hSphereZero_of [NeZero n] : IsZero ((HP.H n).obj (𝕊 0)) :=
  IsZero.of_iso ((biprod_isZero_iff _ _).mpr
    ⟨(HP.isZero_PUnit_of_gt_zero _), (HP.isZero_PUnit_of_gt_zero _)⟩)
    (asIso (hSphereZeroToHPUnitBiprod _ _))

section Reduced

/-- The pair `(𝕊 n, 𝔻 n)` (southern hemisphere). -/
noncomputable abbrev sphereDiskPair := TopPair.of (diskInclusionSphere n) sorry

/-- The pair of punctured sphere and disk `(𝕊* n, 𝔻* n)` (southern hemisphere). -/
noncomputable abbrev puncturedSphereDiskPair :=
  TopPair.of (puncturedDiskInclusionPuncturedSphere n) sorry

/-- The pair `(𝔻 (n + 1), 𝕊 n)`. -/
noncomputable abbrev diskSpherePair :=
  TopPair.of (diskBoundaryInclusion (n + 1)) (isEmbedding_diskBoundaryInclusion _)

/-- The canonical map `reducedH m (𝕊 n) ⟶ H m (𝕊 n, 𝔻 n)`. -/
noncomputable def reducedHSphereToHₚSphereDiskPair :
    (HP.reducedH m).obj (𝕊 n) ⟶ (HP.Hₚ m).obj (sphereDiskPair n) :=
  kernel.ι _ ≫ (HP.iso _).hom.app _ ≫ (HP.Hₚ _).map (sphereDiskPair _).j

/-- The canonical map `reducedH m (𝕊 n) ⟶ H m (𝕊 n, 𝔻 n)` is an isomorphism. -/
instance : IsIso (reducedHSphereToHₚSphereDiskPair HP m n) := sorry

/-- The inclusion `(𝕊* n, 𝔻* n) ⟶ (𝕊 n, 𝔻 n)`. -/
def puncturedSphereDiskPairToSphereDiskPair : puncturedSphereDiskPair n ⟶ sphereDiskPair n := sorry

lemma isEmbedding_puncturedSphereDiskPairToSphereDiskPair :
    IsEmbedding (puncturedSphereDiskPairToSphereDiskPair n) := sorry

/-- The southpole pair inclusion `(∗, ∗) ⟶ (𝕊 n, 𝔻 n)`. -/
noncomputable def diagPUnitToSphereDiskPair :
    diag.obj (of PUnit) ⟶ sphereDiskPair n :=
  TopPair.ofHom (southpoleInclusion n) (diskCenterInclusion n) sorry

lemma isEmbedding_diagPtToSphereDiskPair : IsEmbedding (diagPUnitToSphereDiskPair n) := sorry

lemma isCompl_diagPtToSphereDiskPair :
    TopPair.IsCompl (diagPUnitToSphereDiskPair n) (puncturedSphereDiskPairToSphereDiskPair n) :=
  sorry

/-- The inclusion `(𝕊* n, 𝔻* n) ⟶ (𝕊 n, 𝔻 n)` induces an isomorphism in homology. -/
instance : IsIso ((HP.Hₚ m).map (puncturedSphereDiskPairToSphereDiskPair n)) :=
  HP.isIso_of_closure_interior_of_isCompl (diagPUnitToSphereDiskPair _)
    (puncturedSphereDiskPairToSphereDiskPair _) (isEmbedding_diagPtToSphereDiskPair _)
    (isEmbedding_puncturedSphereDiskPairToSphereDiskPair _) (isCompl_diagPtToSphereDiskPair _) sorry
    _

/-- The homotopy equivalence `((𝕊* (n + 1)), (𝔻* (n + 1))) ≃ₕ (𝔻 (n + 1), 𝕊 n)`. -/
def puncturedSphereDiskPairHomotopyEquiv :
    puncturedSphereDiskPair (n + 1) ≃ₕ diskSpherePair n := sorry

/-- The boundary map `H (m + 1) (𝔻 (n + 1), 𝕊 n) ⟶ reducedH m (𝕊 n)`. -/
noncomputable abbrev hₚDiskSpherePairToReducedHSphere :
    (HP.Hₚ (m + 1)).obj (diskSpherePair n) ⟶ (HP.reducedH m).obj (𝕊 n) :=
  (reducedδ _ _ _).app _

/-- The boundary map `H (m + 1) (𝔻 (n + 1), 𝕊 n) ⟶ reducedH m (𝕊 n)` is an isomorphism. -/
instance : IsIso (hₚDiskSpherePairToReducedHSphere HP m n) := sorry

/-- The map `reducedH (m + 1) (𝕊 (n + 1)) ⟶ reducedH m (𝕊 n)`. -/
noncomputable def reducedHSuccSphereSuccToReducedHSphere :
    (HP.reducedH (m + 1)).obj 𝕊 (n + 1) ⟶ (HP.reducedH m).obj (𝕊 n) :=
  reducedHSphereToHₚSphereDiskPair _ _ _ ≫
  (asIso ((HP.Hₚ _).map (puncturedSphereDiskPairToSphereDiskPair _))).inv ≫
  (IsHomotopyInvariant.hₚIsoOfHomotopyEquiv _ _ (puncturedSphereDiskPairHomotopyEquiv n)).hom ≫
  hₚDiskSpherePairToReducedHSphere _ _ _

/-- The map `reducedH (m + 1) (𝕊 (n + 1)) ⟶ reducedH m (𝕊 n)` is an isomorphism. -/
instance : IsIso (reducedHSuccSphereSuccToReducedHSphere HP m n) := by
  unfold reducedHSuccSphereSuccToReducedHSphere
  infer_instance

/-- The map `reducedH m (𝕊 (k + m)) ⟶ reducedH 0 (𝕊 k)`. -/
noncomputable def reducedHSphereToReducedHZeroSphere :
    (m : ℕ) → (HP.reducedH m).obj (𝕊 (k + m)) ⟶ (HP.reducedH 0).obj (𝕊 k)
  | 0 => 𝟙 _
  | _ + 1 => reducedHSuccSphereSuccToReducedHSphere _ _ _ ≫
      reducedHSphereToReducedHZeroSphere _

/-- The map `reducedH m (𝕊 (k + m)) ⟶ reducedH 0 (𝕊 k)` is an isomorphism. -/
instance : (m : ℕ) → IsIso (reducedHSphereToReducedHZeroSphere HP k m)
  | 0 => by
      unfold reducedHSphereToReducedHZeroSphere
      infer_instance
  | m + 1 => by
      unfold reducedHSphereToReducedHZeroSphere
      have : IsIso (reducedHSphereToReducedHZeroSphere _ _ m) :=
        instIsIsoAbReducedHSphereToReducedHZeroSphere _
      infer_instance

/-- For `k ≠ 0`, `reducedH m (𝕊 (k + m))` is trivial. -/
lemma isZero_reducedHSphere_of' [NeZero k] : (m : ℕ) → IsZero ((HP.reducedH m).obj (𝕊 (k + m)))
  | 0 => sorry
  | _ + 1 => IsZero.of_iso (isZero_reducedHSphere_of' _)
      (asIso (reducedHSphereToReducedHZeroSphere _ _ _))

/-- The map `reducedH (k + n) (𝕊 n) ⟶ reducedH m (𝕊 0)`. -/
noncomputable def reducedHSphereToReducedHSphereZero :
    (n : ℕ) → (HP.reducedH (k + n)).obj (𝕊 n) ⟶ (HP.reducedH k).obj (𝕊 0)
  | 0 => 𝟙 _
  | _ + 1 => reducedHSuccSphereSuccToReducedHSphere _ _ _ ≫
      reducedHSphereToReducedHSphereZero _

/-- The map `reducedH (k + n) (𝕊 n) ⟶ reducedH m (𝕊 0)` is an isomorphism. -/
instance : (n : ℕ) → IsIso (reducedHSphereToReducedHSphereZero HP k n)
  | 0 => by
      unfold reducedHSphereToReducedHSphereZero
      infer_instance
  | n + 1 => by
      unfold reducedHSphereToReducedHSphereZero
      have : IsIso (reducedHSphereToReducedHSphereZero _ _ n) :=
        instIsIsoAbReducedHSphereToReducedHSphereZero _
      infer_instance

/-- For `k ≠ 0`, `reducedH (k + n) (𝕊 n)` is trivial. -/
lemma isZero_reducedHSphere_of'' [NeZero k] : (n : ℕ) → IsZero ((HP.reducedH (k + n)).obj (𝕊 n))
  | 0 =>
      have : Mono (HP.hToHPUnit k (𝕊 0)) := IsZero.mono (isZero_hSphereZero_of _ _) _
      isZero_kernel_of_mono _
  | _ + 1 => IsZero.of_iso (isZero_reducedHSphere_of'' 0)
      (asIso (reducedHSphereToReducedHSphereZero _ _ _))

/-- For `m ≠ n`, `reducedH m (𝕊 n)` is trivial. -/
lemma isZero_reducedHSphere_of {m n} (hmn : m ≠ n) : IsZero ((HP.reducedH m).obj (𝕊 n)) := by
  cases Nat.lt_or_gt.mp hmn
  case inl h =>
    have : n = n - m + m := by lia
    rw [this]
    have : NeZero (n - m) := ⟨by linarith⟩
    exact isZero_reducedHSphere_of' _ (k := n - m) _
  case inr h =>
    have : m = m - n + n := by lia
    rw [this]
    have : NeZero (m - n) := ⟨by linarith⟩
    exact isZero_reducedHSphere_of'' _ (k := m - n) _

/-- The map `reducedH n (𝕊 n) ⟶ coeffObj`. -/
noncomputable def reducedHSphereToCoeffObj :
    (n : ℕ) → (HP.reducedH n).obj (𝕊 n) ⟶ HP.coeffObj
  | 0 => sorry
  | _ + 1 => reducedHSuccSphereSuccToReducedHSphere _ _ _ ≫ reducedHSphereToCoeffObj _

/-- The map `reducedH n (𝕊 n) ⟶ coeffObj` is an isomorphism. -/
instance : (n : ℕ) → IsIso (reducedHSphereToCoeffObj HP n)
  | 0 => sorry
  | n + 1 => by
      unfold reducedHSphereToCoeffObj
      have : IsIso (reducedHSphereToCoeffObj _ n) := instIsIsoAbReducedHSphereToCoeffObj _
      infer_instance

end Reduced

/-- The map `H 0 (𝕊 n) ⟶ coeffObj` for `n ≠ 0`. -/
noncomputable def hZeroSphereToCoeffObj [NeZero n] :
    (HP.H 0).obj (𝕊 n) ⟶ HP.coeffObj :=
  (hIsoReducedHBiprod HP 0 (𝕊 n)).hom ≫
    (isoZeroBiprod (isZero_reducedHSphere_of' HP n 0)).inv

/-- The map `H 0 (𝕊 n) ⟶ coeffObj` is an isomorphism for `n ≠ 0`. -/
instance [NeZero n] : IsIso (hZeroSphereToCoeffObj HP n) := by
  unfold hZeroSphereToCoeffObj
  infer_instance

/-- The map `H n (𝕊 n) ⟶ coeffObj`. -/
noncomputable def hSphereToCoeffObj [NeZero n] :
    (HP.H n).obj (𝕊 n) ⟶ HP.coeffObj :=
  (asIso ((HP.reducedHToH n).app (𝕊 n))).inv ≫ reducedHSphereToCoeffObj HP n

/-- The map `H n (𝕊 n) ⟶ coeffObj` is an isomorphism. -/
instance [NeZero n] : IsIso (hSphereToCoeffObj HP n) := by
  unfold hSphereToCoeffObj
  infer_instance

/-- For `m ≠ n`, `H m (𝕊 n)` is trivial. -/
lemma isZero_HSphere_of [NeZero m] (hmn : m ≠ n) :
    IsZero ((HP.H m).obj (𝕊 n)) :=
  IsZero.of_iso (isZero_reducedHSphere_of _ hmn) (asIso ((reducedHToH _ _).app _)).symm

end EilenbergSteenrod.Spheres
