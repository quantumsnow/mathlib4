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
public import Mathlib.Topology.Category.TopCat.Sphere

@[expose] public section

open CategoryTheory TopCat TopPair CategoryTheory.Limits HomologyPretheory

namespace EilenbergSteenrod.Spheres

universe u v

variable (HP : HomologyPretheory.{u} Ab.{v} (ComplexShape.down ℕ)) [IsEilenbergSteenrod HP] (m n : ℕ)

def isEmbeddingDiskBoundaryInclusion (n : ℕ) : Topology.IsEmbedding (diskBoundaryInclusion n) where
  1 := sorry
  injective := (TopCat.mono_iff_injective _).mp inferInstance

noncomputable abbrev diskSpherePair (n : ℕ) :=
  TopPair.of (diskBoundaryInclusion.{u} n) (isEmbeddingDiskBoundaryInclusion.{u} n)

abbrev sphereDiskHemisphereInclusion (n : ℕ) : 𝔻 n ⟶ 𝕊 n := sorry

noncomputable abbrev sphereDiskPair (n : ℕ) := TopPair.of (sphereDiskHemisphereInclusion n) sorry

def ptInclSphereZeroPos : TopCat.of PUnit ⟶ 𝕊 0 :=
  ofHom {toFun := fun x ↦ ULift.up ⟨!₂[1], by simp; sorry⟩}

def ptInclSphereZeroNeg : TopCat.of PUnit ⟶ 𝕊 0 :=
  ofHom {toFun := fun x ↦ ULift.up ⟨!₂[-1], by simp; sorry⟩}

noncomputable abbrev sphereZeroCofan := BinaryCofan.mk ptInclSphereZeroPos.{u} ptInclSphereZeroNeg

def isColimit_sphereZeroCofan : IsColimit sphereZeroCofan.{u} := sorry

noncomputable def isColimit_HZeroSphereZero : IsColimit ((HP.H 0).mapCocone sphereZeroCofan) :=
  (((IsAdditive.additive_of_small HP WalkingPair 0).preservesColimit).preserves
    isColimit_sphereZeroCofan).some

noncomputable abbrev HZeroSphereZeroCofan' := (Cocone.precomposeEquivalence (pairComp (of PUnit)
  (of PUnit) (HP.H 0))).functor.obj ((HP.H 0).mapCocone sphereZeroCofan)

noncomputable abbrev isColimit_HZeroSphereZero' := (IsColimit.equivOfNatIsoOfIso (pairComp
  (of PUnit) (of PUnit) (HP.H 0)) ((HP.H 0).mapCocone sphereZeroCofan) (HZeroSphereZeroCofan' HP)
  (Iso.refl _) (isColimit_HZeroSphereZero HP))

noncomputable abbrev hZeroSphereZeroToCoeffGroupBiprod :
    (HP.H 0).obj (𝕊 0) ⟶ (HP.coeffGroup) ⊞ (HP.coeffGroup) :=
  (isColimit_HZeroSphereZero' HP).desc
    (BinaryBiproduct.bicone (HP.coeffGroup) (HP.coeffGroup)).toCocone

instance : IsIso (hZeroSphereZeroToCoeffGroupBiprod HP) :=
  (isColimit_HZeroSphereZero' HP).nonempty_isColimit_iff_isIso_desc.mp
    ⟨(BinaryBiproduct.isColimit (HP.coeffGroup) (HP.coeffGroup))⟩

namespace Reduced

noncomputable abbrev hZeroSphereZeroToCoeffGroup := hToHPUnit HP 0 (𝕊 0)

/-- The canonical map `reducedHₘ(Sⁿ) ⟶ Hₘ(Sⁿ, Dⁿ)` -/
noncomputable abbrev reducedHSphereToHₚSphereDiskPair :
    (HP.reducedH m).obj (𝕊 n) ⟶ (HP.Hₚ m).obj (sphereDiskPair n) :=
  kernel.ι _ ≫ (HP.iso _).hom.app _ ≫ (HP.Hₚ _).map (sphereDiskPair _).j

instance : IsIso (reducedHSphereToHₚSphereDiskPair HP m n) := sorry

/-- The composition `Hₘ(Sⁿ, Dⁿ) ⟶ Hₘ(Sⁿ\pt, Dⁿ\pt) ⟶ Hₘ(Dⁿ, Sⁿ⁻¹)`. -/
abbrev hₚSphereDiskPairToHₚDiskSpherePair :
    (HP.Hₚ m).obj (sphereDiskPair n) ⟶ (HP.Hₚ m).obj (diskSpherePair n) := sorry

instance : IsIso (hₚSphereDiskPairToHₚDiskSpherePair HP m n) := sorry

/-- The canonical map `Hₘ₊₁(Dⁿ⁺¹, Sⁿ) ⟶ reducedHₘ(Sⁿ)`. -/
noncomputable abbrev hₚDiskSpherePairToReducedHSphere :
    (HP.Hₚ (m + 1)).obj (diskSpherePair (n + 1)) ⟶ (HP.reducedH m).obj (𝕊 n) :=
  reducedδ.app' HP (m + 1) m (diskSpherePair (n + 1))

instance : IsIso (hₚDiskSpherePairToReducedHSphere HP m n) := sorry

noncomputable abbrev reducedHSuccSphereSuccToReducedHSphere :=
  reducedHSphereToHₚSphereDiskPair HP (m + 1) (n + 1) ≫
    hₚSphereDiskPairToHₚDiskSpherePair HP (m + 1) (n + 1) ≫
    hₚDiskSpherePairToReducedHSphere HP m n

instance : IsIso (reducedHSuccSphereSuccToReducedHSphere HP m n) := inferInstance

--TODO: can use `match` to avoid explicit `(m : ℕ) →` notation?
noncomputable abbrev reducedHSphereToReducedHZeroSphere :
    (k : ℕ) → (HP.reducedH k).obj (𝕊 (n + k)) ⟶ (HP.reducedH 0).obj (𝕊 n)
  | 0 => 𝟙 _
  | k + 1 => reducedHSuccSphereSuccToReducedHSphere HP k (n + k) ≫
      reducedHSphereToReducedHZeroSphere k

instance : (k : ℕ) → IsIso (reducedHSphereToReducedHZeroSphere HP n k)
  | 0 => inferInstance
  | k + 1 => by
      have : IsIso (reducedHSphereToReducedHZeroSphere HP n k) :=
        instIsIsoAbReducedHSphereToReducedHZeroSphere k
      infer_instance

def isZero_reducedHSphere_of' {n} (hn : n > 0) : (k : ℕ) → IsZero ((HP.reducedH k).obj (𝕊 (n + k)))
  | 0 => by
      have : IsZero ((HP.H 0).obj (𝕊 n)) := sorry
      have := IsZero.mono this ((HP.H 0).map (isTerminalPUnit.from (𝕊 n)))
      exact isZero_kernel_of_mono ((HP.H 0).map (isTerminalPUnit.from (𝕊 n)))
  | k + 1 => IsZero.of_iso (isZero_reducedHSphere_of' hn 0)
      (asIso (reducedHSphereToReducedHZeroSphere HP n (k + 1)))

noncomputable abbrev reducedHSphereToReducedHSphereZero :
    (k : ℕ) → (HP.reducedH (m + k)).obj (𝕊 k) ⟶ (HP.reducedH m).obj (𝕊 0)
  | 0 => 𝟙 _
  | k + 1 => reducedHSuccSphereSuccToReducedHSphere HP (m + k) k ≫
      reducedHSphereToReducedHSphereZero k

instance : (k : ℕ) → IsIso (reducedHSphereToReducedHSphereZero HP m k)
  | 0 => inferInstance
  | k + 1 => by
      have : IsIso (reducedHSphereToReducedHSphereZero HP m k) :=
        instIsIsoAbReducedHSphereToReducedHSphereZero k
      infer_instance

def isZero_reducedHSphere_of'' {m} (hm : m > 0) : (k : ℕ) → IsZero ((HP.reducedH (m + k)).obj (𝕊 k))
  | 0 => by
      have : IsZero ((HP.H m).obj (𝕊 0)) := sorry
      have := IsZero.mono this ((HP.H m).map (isTerminalPUnit.from (𝕊 0)))
      exact isZero_kernel_of_mono ((HP.H m).map (isTerminalPUnit.from (𝕊 0)))
  | k + 1 => IsZero.of_iso (isZero_reducedHSphere_of'' hm 0)
      (asIso (reducedHSphereToReducedHSphereZero HP m (k + 1)))

--TODO: fold the proofs for the primed statements into this?
def isZero_reducedHSphere_of {m n} (hmn : m ≠ n) : IsZero ((HP.reducedH m).obj (𝕊 n)) := by
  cases Nat.lt_or_gt.mp hmn
  case inl h =>
    have : n = n - m + m := by lia
    rw [this]
    exact isZero_reducedHSphere_of' HP (n := n - m) (by lia) m
  case inr h =>
    have : m = m - n + n := by lia
    rw [this]
    exact isZero_reducedHSphere_of'' HP (m := m - n) (by lia) n

-- This definition has the disadvantage that `reducedHSphereToCoeffGroup HP n` is not DefEq to `reducedHSphereToReducedHSphereZero HP 0 n ≫ reducedHSphereToCoeffGroup HP 0` but not sure if this will be a problem yet
noncomputable abbrev reducedHSphereToCoeffGroup :
    (n : ℕ) → (HP.reducedH n).obj (𝕊 n) ⟶ HP.coeffGroup
  | 0 => sorry
  | n + 1 => reducedHSuccSphereSuccToReducedHSphere HP n n ≫ reducedHSphereToCoeffGroup n

instance : (n : ℕ) → IsIso (reducedHSphereToCoeffGroup HP n)
  | 0 => sorry
  | n + 1 => by
      have : IsIso (reducedHSphereToCoeffGroup HP n) := instIsIsoAbReducedHSphereToCoeffGroup n
      infer_instance

end Reduced

noncomputable abbrev hZeroSphereToCoeffGroup {n} (hn : n > 0) :
    (HP.H 0).obj (𝕊 n) ⟶ HP.coeffGroup :=
  (asIso (hToReducedHBiprod HP 0 (𝕊 n))).hom ≫
    (isoZeroBiprod (Reduced.isZero_reducedHSphere_of' HP hn 0)).inv

--TODO: is this needed if it can be inferred? If it is needed, should name this something more useful?
instance {n} (hn : n > 0) : IsIso (hZeroSphereToCoeffGroup HP hn) := inferInstance

noncomputable abbrev hSphereToCoeffGroup {n} (hn : n > 0) : (HP.H n).obj (𝕊 n) ⟶ HP.coeffGroup := by
  have := instIsIsoAppTopCatReducedHToHNatOfHasDimensionAxiomOfGtOfNat HP hn (𝕊 n) --TODO: make this inferred automatically?
  exact (asIso ((HP.reducedHToH n).app (𝕊 n))).inv ≫ Reduced.reducedHSphereToCoeffGroup HP n

--TODO: is this needed if it can be inferred? If it is needed, should name this something more useful?
instance {n} (hn : n > 0) : IsIso (hSphereToCoeffGroup HP hn) := inferInstance

def isZero_HSphere_of {m n} (hm : m > 0) (hmn : m ≠ n) : IsZero ((HP.H m).obj (𝕊 n)) := by
  have := instIsIsoAppTopCatReducedHToHNatOfHasDimensionAxiomOfGtOfNat HP hm (𝕊 n) --TODO: make this inferred automatically?
  exact IsZero.of_iso (Reduced.isZero_reducedHSphere_of HP hmn)
    (asIso ((HP.reducedHToH m).app (𝕊 n))).symm

end EilenbergSteenrod.Spheres
