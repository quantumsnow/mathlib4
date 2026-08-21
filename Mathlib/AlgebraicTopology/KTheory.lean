module

public import Mathlib
public import Mathlib.Topology.VectorBundle.Category
public import Mathlib.Topology.Category.Constructions

@[expose] public section

open CategoryTheory Limits Opposite TopPair TopCat NatTrans

namespace KTheory

universe k u v e

variable (𝕜 : Type k) [NontriviallyNormedField 𝕜] (n : ℕ)

/-- The (0th) K-Group of a topological space is the Grothendieck group of the (isomorphism classes
of) finite-rank vector bundles over it. -/
noncomputable def KZero : TopCat.{u}ᵒᵖ ⥤ Ab where
  obj X := ⟨Algebra.GrothendieckAddGroup (Skeleton (FGFixedBaseVectorBundleCat.{k, u} 𝕜 X.unop))⟩
  map f := AddCommGrpCat.ofHom
    (Algebra.GrothendieckAddGroup.lift ((Algebra.GrothendieckAddGroup.of).comp
      (FixedBaseFGVectorBundleCat.pullbackSkeleton 𝕜 f.unop.hom)))
  map_id := sorry
  map_comp := sorry

/-- The (0th) reduced K-Group of a pointed topological space `X` is the kernel of `K(x₀) ⟶ K(X)`,
the induced map of the basepoint inclusion. -/
noncomputable def reducedKZero : TopCat.Pointed.{u}ᵒᵖ ⥤ Ab where
  obj X :=
    kernel ((TopCat.Pointed.forget.op ⋙ KZero 𝕜).map (op (TopCat.Pointed.isInitialPUnit.to X.unop)))
  map f := kernel.lift _ (kernel.ι _ ≫ (TopCat.Pointed.forget.op ⋙ KZero 𝕜).map f) sorry

/-- The `n`th reduced K-Group is the 0th reduced K group of the `n`th suspension. Note that this is
defined on the non-negative integers instead of the non-positive because there is no straightforward
type of non-positive integers so this makes things easier. -/
noncomputable def reducedK : TopCat.Pointed.{u}ᵒᵖ ⥤ Ab :=
  (TopCat.Pointed.suspension' n).op ⋙ reducedKZero 𝕜

example (n : ℕ) : reducedK 𝕜 (n + 1) = (TopCat.Pointed.suspension' n).op ⋙ reducedK 𝕜 1 := rfl

/-- For a pair `(X, A)` with contractible `A`, the quotient projection induces an isomorphism in
reduced K-Groups. -/
instance (Xₚ : TopPair.Pointed.{u}) [ContractibleSpace Xₚ.snd.carrier] :
    IsIso ((reducedK 𝕜 0).map (op (TopCat.Pointed.quotient.out.app Xₚ))) := sorry -- TODO: data

/-- The `n`th relative K-Group is the `n`th reduced K-Group of the quotient of the pair. -/
noncomputable abbrev Kₚ : TopPair.{u}ᵒᵖ ⥤ Ab :=
  TopCat.quotient.op ⋙ reducedK 𝕜 n

/-- The `n`th absolute K-Group of `X` is the `n`th relative K-Group of `(X, ∅)`. This isomorphic to
the `n`th reduced K-Group of `X ⊔ ∗`. -/
noncomputable abbrev K : TopCat.{u}ᵒᵖ ⥤ Ab := incl.op ⋙ Kₚ 𝕜 n

/-- The natural isomorphism `K n X ≅ reducedK n (X ⨿ ∗)`. -/
noncomputable def kIsoReducedKAdjoinPoint :
    K 𝕜 n ≅ TopCat.adjoinPoint.op ⋙ reducedK 𝕜 n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op quotient.inclIsoAdjoinPoint.symm) _

/-- The map `SX ⟶ ΣX` induces an isomorphism in K-Groups. -/
instance (X : TopCat.Pointed.{u}ᵒᵖ) : IsIso ((reducedK 𝕜 0).map (op (TopCat.Pointed.suspension.toReduced.app X.unop))) := sorry -- TODO: data

/-- A shim isomorphism `reducedK (n + 1) Y ≅ reducedK 0 (S(SⁿY))`. -/
noncomputable def proj₂ReducedKIso :
    Pointed.proj₂.op ⋙ reducedK 𝕜 (n + 1) ≅
    (TopPair.Pointed.suspension' n ⋙
      MorphismProperty.Arrow.forget _ _ _ ⋙
        Arrow.leftFunc ⋙
          TopCat.Pointed.forget ⋙
            TopCat.suspension).op ⋙
      reducedK 𝕜 0 :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ((Functor.opComp _ _).symm ≪≫
  NatIso.op (Functor.isoWhiskerRight (TopPair.Pointed.suspension.proj₂Iso' n) _ ≪≫
  Functor.associator _ _ _)) _ ≪≫ Functor.isoWhiskerLeft _ (Functor.leftUnitor _).symm

example : reducedK 𝕜 (n + 1) = (TopCat.Pointed.suspension' n).op ⋙ (TopCat.Pointed.forget ⋙ TopCat.suspension).op ⋙ reducedK 𝕜 0 := rfl

/-- For a pointed pair `(X, Y)`, this is the natural isomorphism
`reducedK (n + 1) Y ≅ reducedK 0 (SⁿX ∪ C(SⁿY))/(SⁿX)`. -/
noncomputable def suspensionProj₂SuspensionReducedKIso :
    (TopPair.Pointed.suspension' n ⋙ MorphismProperty.Arrow.forget _ _ _ ⋙
        Arrow.leftFunc ⋙ TopCat.Pointed.forget ⋙ TopCat.suspension).op ⋙
      reducedK 𝕜 0 ≅
    (TopPair.Pointed.suspension' n ⋙ MorphismProperty.Arrow.forget _ _ _ ⋙
        Pointed.mappingCone.codomPair ⋙ TopPair.Pointed.forget ⋙ quotient).op ⋙
      reducedK 𝕜 0 :=
  Functor.isoWhiskerRight
    (NatIso.op (Functor.isoWhiskerLeft
      (TopPair.Pointed.suspension' n ⋙ MorphismProperty.Arrow.forget _ _ _)
      TopCat.Pointed.mappingCone.codomPairQuotientIso))
    _

/-- The map `reducedK 0 (SⁿX ∪ C(SⁿY)/(SⁿX)) ⟶ reducedK 0 (SⁿX ∪ C(SⁿY))` induced by the quotient
map. -/
noncomputable def suspensionCodomPairQuotientOutReducedK :
    (TopPair.Pointed.suspension' n ⋙
        MorphismProperty.Arrow.forget _ _ _ ⋙ Pointed.mappingCone.codomPair ⋙
          TopPair.Pointed.forget ⋙ quotient).op ⋙
      reducedK 𝕜 0 ⟶
    (TopPair.Pointed.suspension' n ⋙
        MorphismProperty.Arrow.forget _ _ _ ⋙ Pointed.mappingCone.codomPair ⋙
          Pointed.proj₁).op ⋙
      reducedK 𝕜 0 :=
  Functor.whiskerRight
    (NatTrans.op (Functor.whiskerLeft
      (TopPair.Pointed.suspension' n ⋙
        MorphismProperty.Arrow.forget _ _ _ ⋙ Pointed.mappingCone.codomPair)
      TopCat.Pointed.quotient.out))
    _

/-- The map `reducedK (SⁿX ∪ C(SⁿY)/C(SⁿY)) ⟶ reducedK (SⁿX ∪ C(SⁿY))` induced by the quotient map.
-/
noncomputable def suspensionConePairQuotientOutReducedK :
    (TopPair.Pointed.suspension' n ⋙
        MorphismProperty.Arrow.forget _ _ _ ⋙ Pointed.mappingCone.conePair ⋙
          TopPair.Pointed.forget ⋙ quotient).op ⋙
      reducedK 𝕜 0 ⟶
    (TopPair.Pointed.suspension' n ⋙
        MorphismProperty.Arrow.forget _ _ _ ⋙ Pointed.mappingCone.conePair ⋙
          Pointed.proj₁).op ⋙
      reducedK 𝕜 0 :=
  Functor.whiskerRight
    (NatTrans.op (Functor.whiskerLeft
      (TopPair.Pointed.suspension' n ⋙ MorphismProperty.Arrow.forget _ _ _ ⋙
        TopCat.Pointed.mappingCone.conePair)
      TopCat.Pointed.quotient.out))
    _

instance : IsIso (suspensionConePairQuotientOutReducedK 𝕜 n) := sorry -- TODO: data

/-- The natural isomorphism `reducedK 0 (SⁿX ∪ C(SⁿY)/C(SⁿY)) ≅ reducedK 0 SⁿX/SⁿY`. -/
noncomputable def suspensionConePairQuotientReducedKIso :
    (TopPair.Pointed.suspension' n ⋙
        TopPair.Pointed.forget ⋙
          MorphismProperty.Arrow.forget _ _ _ ⋙ mappingCone.conePair ⋙
            quotient).op ⋙
      reducedK 𝕜 0 ≅
    (TopPair.Pointed.suspension' n ⋙
        TopPair.Pointed.forget ⋙
          quotient).op ⋙
      reducedK 𝕜 0 :=
  Functor.isoWhiskerRight
    (NatIso.op (Functor.isoWhiskerLeft
      (TopPair.Pointed.suspension' n ⋙ TopPair.Pointed.forget)
      TopCat.mappingCone.conePairQuotientIso).symm)
    _

/-- A shim associator isomorphism on `reducedK SⁿX/SⁿY`. -/
noncomputable def suspensionForgetIsoQuotientReducedK :
    (TopPair.Pointed.suspension' n ⋙
        TopPair.Pointed.forget ⋙
          quotient).op ⋙
      reducedK 𝕜 0 ≅
    (TopPair.Pointed.forget ⋙
        TopPair.suspension' n ⋙
          quotient).op ⋙
      reducedK 𝕜 0 :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerRight
    (TopPair.Pointed.suspension.forgetIso n) _ ≪≫ Functor.associator _ _ _)) _

/-- The natural isomorphism `reducedK 0 Σⁿ(X/Y) ≅ reducedK 0 SⁿX/SⁿY`. -/
noncomputable def quotientReducedSuspensionReducedKIso :
    (TopPair.Pointed.forget ⋙
        (quotient ⋙ Pointed.suspension.reduced' n)).op ⋙
      reducedK 𝕜 0 ≅
    (TopPair.Pointed.forget ⋙
        (TopPair.suspension' n ⋙ quotient)).op ⋙
      reducedK 𝕜 0 :=
  Functor.isoWhiskerRight
    (NatIso.op (Functor.isoWhiskerLeft
      TopPair.Pointed.forget
      (TopPair.suspension.quotientIso' n)))
    _

/-- The map `reducedK 0 Σⁿ(X/Y) ⟶ reducedK 0 Sⁿ(X/Y)` induced by the quotient map. -/
noncomputable def quotientReducedSuspensionOutReducedK :
    (TopPair.Pointed.forget ⋙ quotient ⋙
        (Pointed.suspension.reduced' n)).op ⋙
      reducedK 𝕜 0 ⟶
    (TopPair.Pointed.forget ⋙ quotient ⋙
        TopCat.Pointed.suspension' n).op ⋙
      reducedK 𝕜 0 :=
  Functor.whiskerRight
    (NatTrans.op (Functor.whiskerLeft
      (TopPair.Pointed.forget ⋙ TopCat.quotient)
      (TopCat.Pointed.suspension.toReduced' n)))
    _

/-- A shim isomorphism `reducedK Sⁿ(X/Y) ≅ Kₚ n (X, Y)`. -/
noncomputable def quotientSuspensionReducedKIso :
    (TopPair.Pointed.forget ⋙
        quotient ⋙
          TopCat.Pointed.suspension' n).op ⋙
      reducedK 𝕜 0 ≅
    TopPair.Pointed.forget.op ⋙ Kₚ 𝕜 n :=
  Functor.isoWhiskerLeft _ (Functor.leftUnitor _) ≪≫
  Functor.isoWhiskerRight (NatIso.op (Functor.associator _ _ _) ≪≫ Functor.opComp _ _ ≪≫
    Functor.isoWhiskerRight (Functor.opComp _ _) _) _ ≪≫
  Functor.associator _ _ _ ≪≫ Functor.associator _ _ _

/-- The boundary map in reduced topological K-Theory. -/
noncomputable def reducedδ :
    Pointed.proj₂.op ⋙ reducedK 𝕜 (n + 1) ⟶
      TopPair.Pointed.forget.op ⋙ Kₚ 𝕜 n :=
  (proj₂ReducedKIso 𝕜 n).hom ≫
  (suspensionProj₂SuspensionReducedKIso 𝕜 n).hom ≫ -- θₙ
  suspensionCodomPairQuotientOutReducedK 𝕜 n ≫ -- mₙ*
  (asIso (suspensionConePairQuotientOutReducedK 𝕜 n)).inv ≫ -- (pₙ*)⁻¹
  (suspensionConePairQuotientReducedKIso 𝕜 n).hom ≫ -- q*
  (suspensionForgetIsoQuotientReducedK 𝕜 n).hom ≫
  (quotientReducedSuspensionReducedKIso 𝕜 n).inv ≫ -- r*
  quotientReducedSuspensionOutReducedK 𝕜 n ≫ -- s*
  (quotientSuspensionReducedKIso 𝕜 n).hom

/-- The isomorphism `K (n + 1) Y ≅ reducedK (n + 1) (Y ⨿ ∗)` for a pair `(X, Y)`. -/
noncomputable def proj₂KIso :
    proj₂.op ⋙ K 𝕜 (n + 1) ≅
    TopPair.adjoinPoint.op ⋙ Pointed.proj₂.op ⋙ reducedK 𝕜 (n + 1) :=
  Functor.isoWhiskerLeft _ (kIsoReducedKAdjoinPoint 𝕜 (n + 1)) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (NatIso.op TopPair.adjoinPoint.proj₂Iso ≪≫ Functor.opComp _ _) _ ≪≫
  Functor.associator _ _ _

/-- The natural isomorphism `Kₚ n (X ⨿ ∗, Y ⨿ ∗) ≅ Kₚ n (X, Y)`. -/
noncomputable def adjoinPointKₚIso :
    TopPair.adjoinPoint.op ⋙ TopPair.Pointed.forget.op ⋙ Kₚ 𝕜 n ≅ Kₚ 𝕜 n :=
  (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (NatIso.op TopPair.adjoinPoint.quotientIso.symm) _

/-- The boundary map in topological K-Theory. -/
noncomputable def δ :
    TopPair.proj₂.op ⋙ K 𝕜 (n + 1) ⟶ Kₚ 𝕜 n :=
  (proj₂KIso 𝕜 n).hom ≫
  TopPair.adjoinPoint.op.whiskerLeft (reducedδ 𝕜 n) ≫
  (adjoinPointKₚIso 𝕜 n).hom

/-- The `CohomologyPretheory` corresponding to topological K-Theory. -/
noncomputable def kTheory : CohomologyPretheory Ab (ComplexShape.down ℕ) where
  Hₚ n := Kₚ 𝕜 n
  H n := K 𝕜 n
  iso _ := Iso.refl _
  δ m n := if h : m = n + 1 then h ▸ δ 𝕜 n else 0

end KTheory
