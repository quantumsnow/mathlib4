/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Topology.Category.TopPair.Pointed
public import Mathlib.Topology.Homotopy.Contractible
/-!
# Constructions on topological spaces

We introduce the following topological constructions
* `adjoinPoint`: the basepoint adjoining functor
* `cylinder`: the cylinder `X × I`
* `quotient`: the quotient of topological spaces via a pushout
* `cone`: the cone `CX := (X × I)/(X × {0})`
* `suspension`: the suspension `CX/(X × {1})`
* `mappingCone`: the mapping cone `X ∪ CY`
* `suspension.reduced`: the reduced suspension (only for pointed spaces)


Most significant gaps/`sorry`s:
* contractibility of the cone
* naturality of a number of maps
* the isomorphism `(X ∪ CY)/X ≅ SY`
* the isomorphism `(X ∪ CY)/CY ≅ X/Y`
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

variable (i j : TopCat.I)

namespace TopCat

/-- The functor on `TopCat` that adjoins a disjoint basepoint. -/
noncomputable def adjoinPoint : TopCat.{u} ⥤ TopCat.Pointed.{u} where
  obj X := ⟨X ⨿ (TopCat.of PUnit), coprod.inr (X := X) PUnit.unit⟩
  map f := ⟨coprod.map f (𝟙 _), sorry⟩

-- TODO: use `HomotopicalAlgebra.Cylinder`?
/-- The cylinder of a topological space `X` is `X × I`. -/
def cylinder : TopCat.{u} ⥤ TopCat.{u} where
  obj X := X ⊗ I
  map f := f ⊗ₘ 𝟙 _

namespace cylinder

/-- The inclusion of a space `X` into its cylinder as `X × {i}`. -/
def sliceIncl : 𝟭 TopCat.{u} ⟶ cylinder where
  app X := TopCat.ofHom ⟨fun x ↦ ⟨x, i⟩, by continuity⟩

/-- The topological pair of a space `X ≅ X × {i}` inside its cylinder. -/
def slicePair : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of ((sliceIncl i).app X) sorry
  map f := TopPair.ofHom (cylinder.map f) f

/-- The topological pair of a space `X ⨿ X ≅ X × {0} ⨿ X × {1}` and the cylinder of `X`. -/
noncomputable def doubleSlicePair : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (A := X ⨿ X) (X := cylinder.obj X) (coprod.desc ((cylinder.sliceIncl 0).app X)
    ((cylinder.sliceIncl 1).app X)) sorry
  map f := TopPair.ofHom (cylinder.map f) (coprod.map f f) sorry

end cylinder

/-- The categorical quotient of of a topological space. Note that this is not always equal to the
topological quotient via `Quotient`. The two will be isomorphic when the collapsed space is nonempty
but whereas `Quotient ⊥` (the quotient by nothing) of a space `X` is isomorpic to `X`, in this
categorical definition, `X/∅ ≅ X ⨿ ∗`. -/
noncomputable def quotient : TopPair.{u} ⥤ TopCat.Pointed.{u} where
  obj Xₚ := ⟨pushout Xₚ.map (isTerminalPUnit.from _), pushout.inr Xₚ.map _ PUnit.unit⟩
  map {Xₚ Yₚ} f := ⟨pushout.map Xₚ.map _ Yₚ.map _ (TopPair.Hom.fst f) (isTerminalPUnit.from _)
    (TopPair.Hom.snd f) (by cat_disch) (by cat_disch), sorry⟩

/-- The canonical map from a space to a quotient of it. -/
noncomputable def quotient.out : TopPair.proj₁ ⟶ quotient ⋙ TopCat.Pointed.forget where
  app _ := pushout.inl _ _
  naturality := sorry

/-- The natural isomorphism `X/∅ ≅ X ⨿ ∗`. -/
noncomputable def quotient.inclIsoAdjoinPoint : TopPair.incl ⋙ TopCat.quotient ≅ adjoinPoint :=
  sorry

/-- The cone of a topological space `X` is the space `CX := (X × I)/(X × {0})` with basepoint the
class `[X × {0}]`. -/
noncomputable def cone : TopCat.{u} ⥤ TopCat.Pointed.{u} := cylinder.slicePair 0 ⋙ quotient

namespace cone

instance (X : TopCat.{u}) : ContractibleSpace (cone.obj X).toTopCat where
  hequiv_unit' := ⟨{
    toFun := ContinuousMap.const _ Unit.unit
    invFun := ContinuousMap.const _ (cone.obj X).basepoint
    left_inv := sorry
    right_inv := sorry
  }⟩

/-- The inclusion of a space `X` into its cone `CX` as `X × {1}`. -/
noncomputable def incl : 𝟭 TopCat.{u} ⟶ cone ⋙ TopCat.Pointed.forget where
  app X := (((cylinder.sliceIncl 1).app X) ≫ quotient.out.app ((cylinder.slicePair 0).obj X))
  naturality := sorry

/-- The topological pair of a space `X ≅ X × {1}` and its cone `CX`. -/
noncomputable abbrev pair : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (cone.incl.app X) sorry
  map f := TopPair.ofHom (cone.map f).toTopCatHom f

end cone

/-- The suspension of a topological space `X` is the space `SX := (X × I)/(X × {0})/(X × {1})` with
basepoint `[X × {1}]`. -/
noncomputable def suspension : TopCat.{u} ⥤ Pointed.{u} where
  obj X := ⟨pushout (cylinder.doubleSlicePair.obj X).hom (coprod.map (isTerminalPUnit.from X)
    (isTerminalPUnit.from X)), pushout.inr (cylinder.doubleSlicePair.obj _).hom _
    (coprod.inr (C := TopCat) PUnit.unit)⟩
  map {X Y} f := ⟨pushout.map _ _ _ _
    (cylinder.map f)
    (coprod.map (isTerminalPUnit.from (TopCat.of PUnit)) (isTerminalPUnit.from (TopCat.of PUnit)))
    (coprod.map f f)
    sorry sorry, sorry⟩

/-- The `n`-fold suspension. -/
noncomputable def suspension' (n : ℕ) : TopCat.{u} ⥤ TopCat.{u} :=
  (suspension ⋙ Pointed.forget).iteratePostcomp n

/-- The canonical map from the cylinder to the suspension. -/
noncomputable def suspension.out : cylinder ⟶ suspension ⋙ Pointed.forget where
  app _ := pushout.inl _ _
  naturality X Y f := sorry

/-- The natural isomorphism `CX/X ≅ SX`. -/
def cone.pairQuotientIso : cone.pair ⋙ quotient ≅ suspension := sorry -- TODO: data

/-- The mapping cone of a map `f : Y ⟶ X` is the gluing of the cone `CY` to `X` along `f`. We will
often denote this by `X ∪ CY`. -/
noncomputable def mappingCone : Arrow TopCat.{u} ⥤ TopCat.{u} where
  obj a := pushout a.hom (cone.incl.app a.left)
  map {a _} f :=
    pushout.map a.hom _ _ _ f.right (cone.map f.left).toTopCatHom f.left (by cat_disch) sorry

namespace mappingCone

/-- The inclusion of the space `X` into the mapping cone `X ∪ CY`. -/
noncomputable def codomIncl : Arrow.rightFunc ⟶ mappingCone where
  app _ := pushout.inl _ _
  naturality := sorry

/-- The topological pair `(X ∪ CY, X)` via the natural inclusion. -/
noncomputable def codomPair : Arrow TopCat.{u} ⥤ TopPair.{u} where
  obj a := TopPair.of (codomIncl.app a) sorry
  map f := TopPair.ofHom (mappingCone.map f) f.right

/-- The natural isomorphism `(X ∪ CY)/X ≅ SY`. -/
def codomPairQuotientIso : codomPair ⋙ quotient ≅ Arrow.leftFunc ⋙ suspension := sorry -- TODO: data

/-- The inclusion of the cone `CY` into the mapping cone `X ∪ CY`. -/
noncomputable def coneIncl : Arrow.leftFunc ⋙ cone ⋙ TopCat.Pointed.forget ⟶ mappingCone where
  app _ := pushout.inr _ _
  naturality := sorry

/-- The topological pair `(X ∪ CY, CY)` via the natural inclusion. -/
noncomputable def conePair : Arrow TopCat.{u} ⥤ TopPair.{u} where
  obj a := TopPair.of (coneIncl.app a) sorry
  map f := TopPair.ofHom (mappingCone.map f) (Pointed.forget.map (cone.map f.left))

/-- For a pair `(X, Y)`, `(X ∪ CY)/CY` is naturally isomorphic to `X/Y` -/
def conePairQuotientIso : MorphismProperty.Arrow.forget _ _ _ ⋙ conePair ⋙ quotient ≅ quotient :=
  sorry

end mappingCone

namespace Pointed

/-- The pointed cylinder of a topological space `X` with basepoint`x₀` is `X × I`, with basepoint
`(x₀, i)`. -/
def cylinder : Pointed.{u} ⥤ Pointed.{u} where
  obj X := ⟨TopCat.cylinder.obj X, ⟨X.basepoint, i⟩⟩
  map f := ⟨TopCat.cylinder.map f.toTopCatHom, sorry⟩

namespace cylinder

/-- The inclusion of `I ≅ I × {x₀}` with basepoint `i` into the cylinder of `X` with basepoint
`x₀`. -/
def intervalIncl : (Functor.const TopCat.Pointed.{u}).obj (I i) ⟶ cylinder i where
  app X := ⟨TopCat.ofHom ⟨fun j ↦ ⟨X.basepoint, j⟩, by continuity⟩, by cat_disch⟩
  naturality := sorry

/-- The topological pair of `I ≅ I × {x₀}` inside the cylinder of `X` with basepoint `x₀`. -/
def intervalPair : Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj X := TopPair.Pointed.of ((intervalIncl i).app X) sorry
  map f := TopPair.Pointed.ofHom ((TopCat.Pointed.cylinder i).map f) (𝟙 (I i))

/-- The inclusion of a pointed space `X` into its cylinder as `X × {i}`. -/
def sliceIncl : 𝟭 Pointed.{u} ⟶ cylinder i where
  app X := ⟨(TopCat.cylinder.sliceIncl i).app X, sorry⟩

/-- The pointed topological pair of a space `X ≅ X × {i}` inside its cylinder. -/
def slicePair : Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj X := TopPair.Pointed.of ((sliceIncl i).app X) sorry
  map f := TopPair.Pointed.ofHom ((cylinder i).map f) f

end cylinder

/-- The canonical pointed map from a pointed space to a quotient of it. -/
noncomputable def quotient.out : TopPair.Pointed.proj₁ ⟶ TopPair.Pointed.forget ⋙ quotient where
  app Xₚ := ⟨TopCat.quotient.out.app Xₚ, sorry⟩

/-- The cone of a topological space `X` with basepoint `x₀` is the space `CX := (X × I)/(X × {0})`
with basepoint `(x₀, 1)`. -/
noncomputable def cone : TopCat.Pointed.{u} ⥤ TopCat.Pointed.{u} where
  obj X := ⟨TopCat.cone.obj X, (TopCat.cone.incl.app X) X.basepoint⟩
  map f := ⟨(TopCat.cone.map f.toTopCatHom).toTopCatHom, sorry⟩

namespace cone

/-- The pointed inclusion of a space `X` into its cone as `X × {1}`. -/
noncomputable def incl : 𝟭 TopCat.Pointed.{u} ⟶ cone where
  app X := ⟨TopCat.cone.incl.app X, sorry⟩

/-- The pointed topological pair of a space `X ≅ X × {1}` and its cone. -/
noncomputable def pair : TopCat.Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj X := TopPair.Pointed.of (cone.incl.app X) sorry
  map f := TopPair.Pointed.ofHom (cone.map f) f

end cone

/-- The `n`-fold suspension. This is defined as an `n`-fold postcomposition with itself rather than
a precomposition because it makes `Sⁿ⁺¹ = SSⁿ` a definitional equality which tends to be more
useful. -/
noncomputable def suspension' (n : ℕ) : Pointed.{u} ⥤ Pointed.{u} :=
  (forget ⋙ suspension).iteratePostcomp n

namespace suspension

/-- The canonical map from the pointed cylinder to the pointed suspension. -/
noncomputable def out : cylinder 1 ⟶ Pointed.forget ⋙ suspension where
  app X := ⟨TopCat.suspension.out.app _, sorry⟩

/-- The inclusion of `I ≅ I × {x₀}` with basepoint `i` into the suspension of `X` with basepoint
`x₀`. -/
noncomputable def intervalIncl :
    (Functor.const TopCat.Pointed.{u}).obj (I 1) ⟶ TopCat.Pointed.forget ⋙ suspension where
  app X := (cylinder.intervalIncl 1).app X ≫ (suspension.out).app X
  naturality := sorry

/-- The pair `(SX, I)` for a pointed space `X`. -/
noncomputable def intervalPair : Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj X := TopPair.Pointed.of (intervalIncl.app X) sorry
  map f := TopPair.Pointed.ofHom (suspension.map f.toTopCatHom) (𝟙 (I 1))

/-- Associator between compositions of `TopCat.Pointed.forget` and `n`-fold suspensions. -/
noncomputable def forgetIso : (n : ℕ) → TopCat.Pointed.forget ⋙ TopCat.suspension' n ≅
    suspension' n ⋙ TopCat.Pointed.forget
  | 0 => Iso.refl _
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (forgetIso n) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm

/-- The reduced suspension of a space pointed `X` is `ΣX := SX/I`. -/
noncomputable def reduced : Pointed.{u} ⥤ Pointed.{u} :=
  intervalPair ⋙ TopPair.Pointed.forget ⋙ quotient

/-- The `n`-fold reduced suspension. -/
noncomputable def reduced' (n : ℕ) : Pointed.{u} ⥤ Pointed.{u} := reduced.iteratePostcomp n

/-- The natural map from the suspension to the reduced suspension. -/
noncomputable abbrev toReduced : TopCat.Pointed.forget ⋙ suspension ⟶ reduced :=
  intervalPair.whiskerLeft quotient.out

/-- The natural map from the `n`-fold suspension to the `n`-fold reduced suspension. -/
noncomputable abbrev toReduced' (n : ℕ) : suspension' n ⟶ reduced' n := match n with
  | 0 => 𝟙 _
  | n + 1 => toReduced' n ◫ toReduced

end suspension

/-- The mapping cone of a map `f : Y ⟶ X` is the gluing of the cone of `Y` to `X` along `f`. We will
often denote this by `X ∪ CY`. -/
noncomputable def mappingCone : Arrow TopCat.Pointed.{u} ⥤ TopCat.Pointed.{u} where
  obj a := ⟨TopCat.mappingCone.obj (forgetArrow.obj a), (TopCat.mappingCone.codomIncl.app
    (forgetArrow.obj a)) a.right.basepoint⟩
  map f := ⟨TopCat.mappingCone.map (forgetArrow.map f), sorry⟩

namespace mappingCone

/-- The pointed inclusion of `X ⟶ X ∪ CY`. -/
noncomputable def codomIncl : Arrow.rightFunc ⟶ mappingCone where
  app a := ⟨TopCat.mappingCone.codomIncl.app (forgetArrow.obj a), sorry⟩

/-- The pointed topological pair `(X ∪ CY, X)` via the natural inclusion. -/
noncomputable def codomPair : Arrow TopCat.Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj a := TopPair.Pointed.of (codomIncl.app a) sorry
  map f := TopPair.Pointed.ofHom (mappingCone.map f) f.right

/-- The natural isomorphism `(X ∪ CY)/X ≅ SY`. -/
def codomPairQuotientIso :
    codomPair ⋙ TopPair.Pointed.forget ⋙ quotient ≅
      Arrow.leftFunc ⋙ TopCat.Pointed.forget ⋙ suspension := sorry

/-- The pointed inclusion `CY ⟶ X ∪ CY`. -/
noncomputable def coneIncl : Arrow.leftFunc ⋙ cone ⟶ mappingCone where
  app a := ⟨TopCat.mappingCone.coneIncl.app (forgetArrow.obj a), sorry⟩

/-- The pointed topological pair `(X ∪ CY, CY)` via the natural inclusion. -/
noncomputable def conePair : Arrow TopCat.Pointed.{u} ⥤ TopPair.Pointed.{u} where
  obj a := TopPair.Pointed.of (coneIncl.app a) sorry
  map f := TopPair.Pointed.ofHom (mappingCone.map f) (cone.map f.left)

/-- Forgetting the basepoint of the pointed mapping cone is the same as the unpointed mapping cone.
-/
noncomputable def forgetConePairIso :
    MorphismProperty.Arrow.forget _ _ _ ⋙ TopCat.Pointed.mappingCone.conePair ⋙
      TopPair.Pointed.forget ≅
    TopPair.Pointed.forget ⋙ MorphismProperty.Arrow.forget _ _ _ ⋙ TopCat.mappingCone.conePair :=
  NatIso.ofComponents (fun Xₚ ↦ { hom := 𝟙 _, inv := 𝟙 _ })

end mappingCone

end Pointed

end TopCat

namespace TopPair

/-- The pairwise adjoining of basepoints to topological spaces. -/
noncomputable def adjoinPoint : TopPair.{u} ⥤ TopPair.Pointed.{u} where
  obj Xₚ := TopPair.Pointed.of (TopCat.adjoinPoint.map Xₚ.map) sorry
  map f := TopPair.Pointed.ofHom (TopCat.adjoinPoint.map f.right) (TopCat.adjoinPoint.map f.left)

namespace adjoinPoint

/-- The first space of the pair with adjoined baspoints is the same as adjoining a basepoint to the
first space. -/
noncomputable def proj₁Iso : adjoinPoint ⋙ TopPair.Pointed.proj₁ ≅ proj₁ ⋙ TopCat.adjoinPoint :=
  Iso.refl _

/-- The second space of the pair with adjoined baspoints is the same as adjoining a basepoint to the
second space. -/
noncomputable def proj₂Iso : adjoinPoint ⋙ TopPair.Pointed.proj₂ ≅ proj₂ ⋙ TopCat.adjoinPoint :=
  Iso.refl _

/-- The quotient of a topological pair with adjoined basepoints is isomorphic to the same pair
without adjoining basepoints. -/
def quotientIso :
    TopPair.adjoinPoint ⋙ TopPair.Pointed.forget ⋙ TopCat.quotient ≅ TopCat.quotient := sorry

end adjoinPoint

/-- The pairwise suspension of topological spaces. See `TopCat.suspension` for what the suspension
is on `TopCat`. -/
noncomputable def suspension : TopPair.{u} ⥤ TopPair.Pointed.{u} where
  obj Xₚ := TopPair.Pointed.of (TopCat.suspension.map Xₚ.map) sorry
  map f := TopPair.Pointed.ofHom (TopCat.suspension.map f.right) (TopCat.suspension.map f.left)

/-- The `n`-fold pairwise suspension. -/
noncomputable def suspension' (n : ℕ) : TopPair.{u} ⥤ TopPair.{u} :=
  (suspension ⋙ Pointed.forget).iteratePostcomp n

namespace suspension

/-- The quotient of the the pairwise suspension is isomorphic to the reduced suspension of the
quotient. -/
def quotientIso : TopPair.suspension ⋙ TopPair.Pointed.forget ⋙ TopCat.quotient ≅
    TopCat.quotient ⋙ TopCat.Pointed.suspension.reduced := sorry

/-- The quotient of the the `n`-fold pairwise suspension is isomorphic to the `n`-fold reduced
suspension of the quotient. -/
noncomputable def quotientIso' : (n : ℕ) →
    (suspension' n) ⋙ TopCat.quotient ≅ TopCat.quotient ⋙ TopCat.Pointed.suspension.reduced' n
  | 0 => Iso.refl _
  | n + 1 => Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ quotientIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (quotientIso' n) _

/-- The first space of a pairwise suspension is the same as the suspension of the first space. -/
noncomputable def proj₁Iso : suspension ⋙ Pointed.proj₁ ≅ proj₁ ⋙ TopCat.suspension := Iso.refl _

/-- The second space of a pairwise suspension is the same as the suspension of the second space. -/
noncomputable def proj₂Iso : suspension ⋙ Pointed.proj₂ ≅ proj₂ ⋙ TopCat.suspension := Iso.refl _

end suspension

namespace Pointed

/-- The `n`-fold suspension of pointed pairs. -/
noncomputable def suspension' (n : ℕ) : Pointed.{u} ⥤ Pointed.{u} :=
  (forget ⋙ suspension).iteratePostcomp n

namespace suspension

/-- Associator between compositions of `TopPair.Pointed.forget` and `n`-fold suspensions. -/
noncomputable def forgetIso : (n : ℕ) → TopPair.Pointed.forget ⋙ TopPair.suspension' n ≅
    suspension' n ⋙ TopPair.Pointed.forget
  | 0 => Iso.refl _
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (forgetIso n) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm

/-- The first space of a pairwise suspension of a pointed pair is the same as the suspension of the
second space. -/
noncomputable def proj₁Iso : TopPair.Pointed.forget ⋙ TopPair.suspension ⋙ Pointed.proj₁ ≅
    Pointed.proj₁ ⋙ TopCat.Pointed.forget ⋙ TopCat.suspension :=
  Functor.isoWhiskerLeft _ TopPair.suspension.proj₁Iso ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Pointed.proj₁ForgetIso.symm _

/-- The first space of a pairwise suspension of a pointed pair is the same as the `n`-fold
suspension of the second space. -/
noncomputable def proj₁Iso' : (n : ℕ) →
    suspension' n ⋙ Pointed.proj₁ ≅ Pointed.proj₁ ⋙ TopCat.Pointed.suspension' n
  | 0 => Iso.refl _
  | n + 1 => Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ proj₁Iso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (proj₁Iso' n) _

/-- The second space of a pairwise suspension of a pointed pair is the same as the suspension of the
second space. -/
noncomputable def proj₂Iso :
    TopPair.Pointed.forget ⋙ TopPair.suspension ⋙ Pointed.proj₂ ≅
      Pointed.proj₂ ⋙ TopCat.Pointed.forget ⋙ TopCat.suspension :=
  Functor.isoWhiskerLeft _ TopPair.suspension.proj₂Iso ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight Pointed.proj₂ForgetIso.symm _

/-- The second space of a pairwise suspension of a pointed pair is the same as the `n`-fold
suspension of the second space. -/
noncomputable def proj₂Iso' : (n : ℕ) →
    suspension' n ⋙ Pointed.proj₂ ≅ Pointed.proj₂ ⋙ TopCat.Pointed.suspension' n
  | 0 => Iso.refl _
  | n + 1 => Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ proj₂Iso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (proj₂Iso' n) _

end suspension

end Pointed

end TopPair
