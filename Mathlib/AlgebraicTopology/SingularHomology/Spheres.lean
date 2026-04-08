/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/

module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.Topology.EilenbergSteenrod
public import Mathlib.Topology.Category.TopCat.Sphere

@[expose] public section

open CategoryTheory TopCat

namespace SingularHomology.Spheres

variable (Hₚ : ℕ → TopPair ⥤ Ab) (H : ℕ → TopCat ⥤ Ab) (H_incl_Hₚ : ∀ n : ℕ, H n ≅ TopPair.incl ⋙ Hₚ n)
  (δ : (Π m n, (Hₚ m) ⟶ TopPair.proj₂ ⋙ H n))
  (es : IsEilenbergSteenrod Hₚ H H_incl_Hₚ δ)

def homology_zero_sphere_zero : (H 0).obj (𝕊 0) ≅ ⟨ℤ⟩ ⊞ ⟨ℤ⟩ := by
  sorry

def homology_zero (n : ℕ) : (H 0).obj (𝕊 n) ≅ ⟨ℤ⟩ := by
  sorry

def homology_n (n : ℕ) : (H n).obj (𝕊 n) ≅ ⟨ℤ⟩ := sorry

def homology_m (m : ℕ) (n : ℕ) (h : m ≠ n) : Limits.IsZero ((H m).obj (𝕊 n)) := sorry

end SingularHomology.Spheres
