module

public import Mathlib
public import Mathlib.Topology.Category.TopCat.Pointed.Basic

@[expose] public section

open CategoryTheory TopPair Opposite

universe u

namespace TopPair

abbrev Pointed :=
  MorphismProperty.Arrow TopCat.Pointed.isEmbedding ⊤ ⊤

namespace Pointed

variable {Xₚ Yₚ : Pointed.{u}}

/-- The first space of the pair -/
abbrev fst : TopCat.Pointed.{u} := Xₚ.right

/-- The second space of the pair -/
abbrev snd : TopCat.Pointed.{u} := Xₚ.left

/-- The embedding of the second into the first space -/
abbrev map : Xₚ.snd ⟶ Xₚ.fst := Xₚ.hom

lemma isEmbedding_map (X : Pointed.{u}) : Topology.IsEmbedding X.map.hom := X.prop

/-- Construct a pointed topological pair from its components. -/
abbrev of {A X : TopCat.Pointed.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f.hom) : Pointed.{u} :=
  MorphismProperty.Arrow.mk (P := TopCat.Pointed.isEmbedding) f h

/-- Construct a morphism in `TopPair.Pointed` from its components. -/
abbrev ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

/-- The map between the first spaces -/
abbrev Hom.fst (f : Xₚ ⟶ Yₚ) : Xₚ.fst ⟶ Yₚ.fst := f.hom.right

@[simp]
lemma Hom.fst_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) : Hom.fst (ofHom f g) = f := rfl

/-- The map between the second spaces -/
abbrev Hom.snd (f : Xₚ ⟶ Yₚ) : Xₚ.snd ⟶ Yₚ.snd := f.hom.left

@[simp]
lemma Hom.snd_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f := by cat_disch) : Hom.snd (ofHom f g) = g := rfl

@[reassoc, elementwise]
lemma Hom.w (f : Xₚ ⟶ Yₚ) :
    Hom.snd f ≫ Yₚ.map = Xₚ.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

def toTopPair (Xₚ : Pointed.{u}) : TopPair.{u} := TopPair.of Xₚ.map.toTopCatHom sorry

def Hom.toTopPairHom {Xₚ Yₚ : Pointed.{u}} (f : Xₚ ⟶ Yₚ) : (Xₚ.toTopPair ⟶ Yₚ.toTopPair) := TopPair.ofHom (Hom.fst f).toTopCatHom (Hom.snd f).toTopCatHom sorry

instance : Coe Pointed.{u} TopPair.{u} where
  coe := toTopPair

instance {Xₚ Yₚ : Pointed.{u}} : Coe (Xₚ ⟶ Yₚ) ((Xₚ : TopPair) ⟶ Yₚ) where
  coe := Hom.toTopPairHom

abbrev forget : Pointed.{u} ⥤ TopPair.{u} where
  obj X := X
  map f := f

def proj₁ : Pointed.{u} ⥤ TopCat.Pointed.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

-- `simps` generates the wrong lemmas
@[simp]
lemma proj₁_obj (Xₚ : Pointed.{u}) : proj₁.obj Xₚ = Xₚ.fst := rfl

@[simp]
lemma proj₁_map (f : Xₚ ⟶ Yₚ) : proj₁.map f = Hom.fst f := rfl

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
lemma proj₂_op_map {Xₚ Yₚ : Pointed.{u}ᵒᵖ} (f : Xₚ ⟶ Yₚ) : (proj₂.op.map f) = (Hom.snd f.unop).op := rfl

/-- Unpointed and pointed projection and forgetting are compatible. -/
def proj₁ForgetIso : proj₁ ⋙ TopCat.Pointed.forget ≅ forget ⋙ TopPair.proj₁ := Iso.refl _

/-- Unpointed and pointed projection and forgetting are compatible. -/
def proj₂ForgetIso : proj₂ ⋙ TopCat.Pointed.forget ≅ forget ⋙ TopPair.proj₂ := Iso.refl _

-- TODO: the following needs updated docstrings
abbrev HomologyCategory (P : ObjectProperty TopCat.{u}) [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderFiniteCoproducts] :=
  MorphismProperty.Arrow (TopCat.Pointed.HomologyCategory.isEmbedding P) ⊤ ⊤

namespace HomologyCategory

variable {P : ObjectProperty TopCat.{u}} {J : Type*} [P.IsClosedUnderFiniteProducts] [P.IsClosedUnderFiniteCoproducts] (X Y : HomologyCategory.{u} P)

/-- The first space of the pair -/
abbrev fst : TopCat.Pointed.HomologyCategory P := X.right

/-- The second space of the pair -/
abbrev snd : TopCat.Pointed.HomologyCategory P := X.left

/-- The embedding of the second into the first space -/
abbrev map : X.snd ⟶ X.fst := X.hom

lemma isEmbedding_map : Topology.IsEmbedding X.map.hom.toTopCatHom.hom := X.prop

/-- Construct a topological pair from its components. -/
abbrev of {A X : TopCat.Pointed.HomologyCategory P} (f : A ⟶ X) (h : TopCat.Pointed.HomologyCategory.isEmbedding _ f) : HomologyCategory.{u} P :=
  MorphismProperty.Arrow.mk (P := TopCat.Pointed.HomologyCategory.isEmbedding _) f h

-- /-- Constructor for a topological pair (X, A) where A ⊆ X. -/
-- abbrev ofSubset {X : HomologyCategory P} (A : Set X.obj) : TopPair.Pointed.HomologyCategory.{u} P := of (A := (TopCat.of A))
--   (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

-- def ofSubsetRangeIso (Xₚ : TopPair.Pointed.HomologyCategory.{u} P) : ofSubset (Set.range Xₚ.map) ≅ Xₚ := sorry

/-- Constructs the topological pair `(X, ∅)` from `X : TopCat`. -/
abbrev ofTopCat (X : TopCat.Pointed.HomologyCategory P) : HomologyCategory.{u} P :=
  of ((TopCat.Pointed.HomologyCategory.isInitialPUnit P).to X) sorry

variable {X Y : HomologyCategory.{u} P}

/-- Construct a morphism in `TopPair` from its components. -/
abbrev ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

/-- The map between the first spaces -/
abbrev Hom.fst (f : X ⟶ Y) : X.fst ⟶ Y.fst := f.hom.right

@[simp]
lemma Hom.fst_ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) : Hom.fst (ofHom f g) = f := rfl

/-- The map between the second spaces -/
abbrev Hom.snd (f : X ⟶ Y) : X.snd ⟶ Y.snd := f.hom.left

@[simp]
lemma Hom.snd_ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) : Hom.snd (ofHom f g) = g := rfl

@[reassoc, elementwise]
lemma Hom.w {X Y : HomologyCategory.{u} P} (f : X ⟶ Y) :
    Hom.snd f ≫ Y.map = X.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

def forget : HomologyCategory P ⥤ Pointed.{u} where
  obj X := TopPair.Pointed.of X.map.hom X.prop
  map f := TopPair.Pointed.ofHom (Hom.fst f).hom (Hom.snd f).hom sorry

/-- The functor from topological pairs to topological spaces that forgets the second space, i.e. the
projection to the first space. -/
def proj₁ : HomologyCategory.{u} P ⥤ TopCat.Pointed.HomologyCategory P :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

-- `simps` generates the wrong lemmas
@[simp]
lemma proj₁_obj (X : HomologyCategory.{u} P) : proj₁.obj X = X.fst := rfl

@[simp]
lemma proj₁_map (f : X ⟶ Y) : proj₁.map f = Hom.fst f := rfl

/-- The functor from topological pairs to topological spaces that forgets the first space, i.e. the
projection to the second space. -/
def proj₂ : HomologyCategory.{u} P ⥤ TopCat.Pointed.HomologyCategory P :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

-- simps generates the wrong lemmas
@[simp]
lemma proj₂_obj (X : HomologyCategory.{u} P) : proj₂.obj X = X.snd := rfl

@[simp]
lemma proj₂_map (f : X ⟶ Y) : proj₂.map f = Hom.snd f := rfl

-- simps generates the wrong lemmas
@[simp]
lemma proj₂_op_obj (X : (HomologyCategory.{u} P)ᵒᵖ) : (proj₂.op.obj X) = op X.unop.snd := rfl

@[simp]
lemma proj₂_op_map {X Y : (HomologyCategory.{u} P)ᵒᵖ} (f : X ⟶ Y) : (proj₂.op.map f) = (Hom.snd f.unop).op := rfl

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
def incl : TopCat.Pointed.HomologyCategory P ⥤ HomologyCategory.{u} P where
  obj X := ofTopCat X
  map f := ofHom f (𝟙 _) sorry

/-- The functor from topological spaces to topological pairs that sends a space X to the identity
morphism on X. -/
abbrev diag : TopCat.Pointed.HomologyCategory P ⥤ HomologyCategory.{u} P where
  obj X := of (𝟙 X) Topology.IsEmbedding.id
  map f := ofHom f f

-- set_option backward.defeqAttrib.useBackward true in
-- /-- The inclusion functor is left adjoint to the projection to the first component. -/
-- @[simps]
-- def inclAdjProj₁ : incl (P := P) ⊣ proj₁ where
--   unit.app X := 𝟙 X
--   counit.app X := ofHom (𝟙 X.fst) ((TopCat.Pointed.HomologyCategory.isInitialPEmpty P).to X.snd)

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
@[simps]
def proj₁AdjDiag : proj₁ (P := P) ⊣ diag where
  unit.app X := ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism (X, ∅) ⟶ (X, A) that is the identity on X. -/
abbrev inclFst (X : HomologyCategory.{u} P) : incl.obj X.fst ⟶ X :=
  ofHom (𝟙 _) ((TopCat.Pointed.HomologyCategory.isInitialPUnit P).to _)

-- /-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
-- the second space that fit in a commutative square with the maps of the pairs. -/
-- abbrev Homotopy (f g : X ⟶ Y) := TopPair.Homotopy (forget.map f) (forget.map g)

-- attribute [reassoc, elementwise] Homotopy.w
-- attribute [local simp] Homotopy.w Homotopy.w_apply

-- namespace Homotopy

-- @[local simp]
-- lemma w_apply' {f g : X ⟶ Y} (H : Homotopy f g) (x : X.snd.obj) (t : unitInterval) :
--     H.fst (t, X.map x) = Y.map (H.snd (t, x)) := by
--   have := w_apply H (x, I.homeomorph.symm t)
--   sorry-- cat_disch

-- /-- Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
-- `TopCat.Homotopy.refl` on the first and second components.
-- -/
-- @[simps]
-- def refl (f : X ⟶ Y) : Homotopy f f where
--   fst := TopCat.Homotopy.refl (Hom.fst f)
--   snd := TopCat.Homotopy.refl (Hom.snd f)

-- instance : Inhabited (Homotopy (𝟙 X) (𝟙 X)) :=
--   ⟨Homotopy.refl _⟩

-- /-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `TopCat.Homotopy.symm` on
-- the first and second components.
-- -/
-- @[simps]
-- def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
--   fst := F.fst.symm
--   snd := F.snd.symm

-- @[simp]
-- theorem symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
--   cat_disch

-- theorem symm_bijective {f₀ f₁ : X ⟶ Y} :
--     Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
--   Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

-- /--
-- Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
-- `TopCat.Homotopy.trans` on the first and second components.
-- -/
-- @[simps]
-- noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
--     Homotopy f₀ f₂ where
--   fst := F.fst.trans G.fst
--   snd := F.snd.trans G.snd
--   w := by
--     ext ⟨_, _⟩
--     simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
--     cat_disch

-- theorem symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
--     (F.trans G).symm = G.symm.trans F.symm := by
--       ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

-- set_option backward.isDefEq.respectTransparency false in
-- /-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, we can define a
-- `Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)` by `TopCat.Homotopy.comp` on the first and second components.
-- -/
-- @[simps]
-- def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
--     Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where
--   fst := G.fst.comp F.fst
--   snd := G.snd.comp F.snd

-- end Homotopy

-- /-- Two maps between topological pairs are homotopic if there is a homotopy between them. -/
-- def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

-- namespace Homotopic

-- /-- Two maps of topological pairs being homotopic defines an equivalence relation. -/
-- theorem equivalence : Equivalence (Homotopic (X := X) (Y := Y)) :=
--   ⟨fun f ↦ ⟨Homotopy.refl f⟩, fun h ↦ h.map Homotopy.symm, fun h₀ h₁ ↦ h₀.map2 Homotopy.trans h₁⟩

-- abbrev homRel : HomRel (TopPair.Pointed.HomologyCategory.{u} P) := fun _ _ ↦ Homotopic

-- instance : HomRel.IsStableUnderPrecomp homRel := ⟨fun _ _ _ h ↦ ⟨.comp h.some (.refl _)⟩⟩

-- instance : HomRel.IsStableUnderPostcomp homRel := ⟨fun _ h ↦ ⟨.comp (.refl _) h.some⟩⟩

-- abbrev TopPairHomotopyCat := CategoryTheory.Quotient homRel

-- abbrev HomotopyEquiv (X Y : TopPair.Pointed.HomologyCategory.{u} P) :=
--   Iso (C := TopPairHomotopyCat) ((Quotient.functor _).obj X) ((Quotient.functor _).obj Y)

-- @[inherit_doc] scoped infixl:25 " ≃ₕ " => HomotopyEquiv

-- end Homotopic

-- section Embedding

-- /-- A morphism `f : X ⟶ Y` in `TopPair` is an embedding if its first and second component are
-- embeddings. -/
-- abbrev IsEmbedding {X Y : HomologyCategory.{u} P} (f : X ⟶ Y) := TopPair.Pointed.IsEmbedding (forget.map f)

-- end Embedding

-- section Complement

-- /-- Two morphisms `f : A ⟶ X` and `g : B ⟶ X` in `TopPair` are complements if their first and second
-- components are complements in `TopCat`. -/
-- protected abbrev IsCompl {X A B : HomologyCategory.{u} P} (f : A ⟶ X) (g : B ⟶ X) := TopPair.Pointed.IsCompl (forget.map f) (forget.map g)

-- end Complement

end HomologyCategory

end Pointed

-- abbrev FirstPointed := MorphismProperty.Comma (𝟭 TopCat.{u}) (TopCat.Pointed.forget.{u}) TopCat.isEmbedding ⊤ ⊤

-- namespace FirstPointed

-- variable {Xₚ Yₚ : FirstPointed}

-- abbrev fst : TopCat.Pointed.{u} := Xₚ.right

-- abbrev snd : TopCat.{u} := Xₚ.left

-- abbrev map : Xₚ.snd ⟶ Xₚ.fst := Xₚ.hom

-- abbrev of {A : TopCat.{u}} {X : TopCat.Pointed.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f) : FirstPointed :=
--   MorphismProperty.Comma.mk (P := TopCat.isEmbedding) (Comma.mk A X f) h

-- def rightPointedMapOfLeftPointedMap {X : TopCat.{u}} {Y : TopCat.Pointed.{u}} (f : ↑Y ⟶ X) : ↑Y ⟶ ((⟨X, f Y.point⟩ : TopCat.Pointed.{u}) : TopCat) := f

-- abbrev ofLeftPointed {X : TopCat.{u}} {Y : TopCat.Pointed.{u}} (f : ↑Y ⟶ X) : FirstPointed := FirstPointed.of (rightPointedMapOfLeftPointedMap f) sorry

-- /-- Construct a morphism in `TopPair.FirstPointed` from its components. -/
-- abbrev ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f.toHom := by cat_disch) : Xₚ ⟶ Yₚ :=
--   ⟨⟨g, f, w⟩, by trivial, by trivial⟩

-- /-- The map between the first spaces -/
-- abbrev Hom.fst (f : Xₚ ⟶ Yₚ) : Xₚ.fst ⟶ Yₚ.fst := f.hom.right

-- @[simp]
-- lemma Hom.fst_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f.toHom := by cat_disch) : Hom.fst (ofHom f g) = f := rfl

-- /-- The map between the second spaces -/
-- abbrev Hom.snd (f : Xₚ ⟶ Yₚ) : Xₚ.snd ⟶ Yₚ.snd := f.hom.left

-- @[simp]
-- lemma Hom.snd_ofHom (f : Xₚ.fst ⟶ Yₚ.fst) (g : Xₚ.snd ⟶ Yₚ.snd) (w : g ≫ Yₚ.map = Xₚ.map ≫ f.toHom := by cat_disch) : Hom.snd (ofHom f g) = g := rfl

-- @[reassoc, elementwise]
-- lemma Hom.w {X Y : FirstPointed.{u}} (f : X ⟶ Y) :
--     Hom.snd f ≫ Y.map = X.map ≫ (Hom.fst f).toHom :=
--   f.hom.w

-- attribute [local simp] Hom.w_apply

-- instance : Coe FirstPointed TopPair.{u} where
--   coe Xₚ := TopPair.of Xₚ.map Xₚ.prop

-- def forget : FirstPointed ⥤ TopPair.{u} where
--   obj := Coe.coe
--   map f := TopPair.ofHom f.right.toHom f.left sorry

-- instance : Coe (Xₚ ⟶ Yₚ) ((Xₚ : TopPair) ⟶ Yₚ) where
--   coe f := TopPair.ofHom (Hom.fst f).toHom (Hom.snd f) f.w

-- def proj₁ : FirstPointed.{u} ⥤ TopCat.Pointed.{u} :=
--   MorphismProperty.Comma.forget _ _ _ _ _ ⋙ CategoryTheory.Comma.snd _ _

-- -- `simps` generates the wrong lemmas
-- @[simp]
-- lemma proj₁_obj (Xₚ : FirstPointed.{u}) : proj₁.obj Xₚ = Xₚ.fst := rfl

-- @[simp]
-- lemma proj₁_map (f : Xₚ ⟶ Yₚ) : proj₁.map f = Hom.fst f := rfl

-- def proj₂ : FirstPointed.{u} ⥤ TopCat.{u} :=
--   MorphismProperty.Comma.forget _ _ _ _ _ ⋙ CategoryTheory.Comma.fst _ _

-- -- simps generates the wrong lemmas
-- @[simp]
-- lemma proj₂_obj (Xₚ : FirstPointed.{u}) : proj₂.obj Xₚ = Xₚ.snd := rfl

-- @[simp]
-- lemma proj₂_map (f : Xₚ ⟶ Yₚ) : proj₂.map f = Hom.snd f := rfl

-- -- simps generates the wrong lemmas
-- @[simp]
-- lemma proj₂_op_obj (Xₚ : FirstPointed.{u}ᵒᵖ) : (proj₂.op.obj Xₚ) = op Xₚ.unop.snd := rfl

-- @[simp]
-- lemma proj₂_op_map {Xₚ Yₚ : FirstPointed.{u}ᵒᵖ} (f : Xₚ ⟶ Yₚ) : (proj₂.op.map f) = (Hom.snd f.unop).op := rfl

-- end FirstPointed

end TopPair
