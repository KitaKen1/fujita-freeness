/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedEmbeddingSheafExactness
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
All-degree cohomology of the pushforward of an actual abelian sheaf along a
closed topological embedding. The exact pullback/pushforward adjunction gives
an Ext equivalence. Pullback of a constant sheaf is identified with the
constant sheaf by uniqueness of left adjoints to global sections.
This is an additive comparison, natural in the coefficient sheaf.
Finite dimensionality and upper-degree vanishing are separate questions.
-/

@[expose] public section
open CategoryTheory Limits TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : TopCat.{u}}

noncomputable def abelianSheafPushforwardGlobalSectionsIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

noncomputable def abelianSheafPullbackConstantIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} f ≅
      constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).ofNatIsoRight
      (abelianSheafPushforwardGlobalSectionsIso f)).leftAdjointUniq
        (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop)

theorem abelianSheaf_pullback_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  unfold TopCat.Sheaf.pullback
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (Opens.map f) AddCommGrpCat.{u} (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X)

theorem abelianSheaf_pullback_additive (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive := by
  let := abelianSheaf_pullback_preservesFiniteLimits f
  exact Functor.additive_of_preserves_binary_products _

noncomputable def closedEmbeddingCohomologyAddEquiv {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n ≃+
      Sheaf.H.{u} F n := by
  let := abelianSheaf_pushforward_additive f
  let := abelianSheaf_pullback_additive f
  let := abelianSheaf_pullback_preservesFiniteLimits f
  let := closedEmbeddingPushforwardPreservesFiniteColimits hf
  let e := (abelianSheafPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  exact (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).extEquiv.symm.trans
    (((Abelian.extFunctor n).mapIso e.symm.op).app F).addCommGroupIsoToAddEquiv

theorem closedEmbeddingCohomologyAddEquiv_naturality {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) {F G : X.Sheaf AddCommGrpCat.{u}}
    (φ : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) n) :
    closedEmbeddingCohomologyAddEquiv hf G n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map φ) n x) =
      Sheaf.H.map φ n (closedEmbeddingCohomologyAddEquiv hf F n x) := by
  let := abelianSheaf_pushforward_additive f
  let := abelianSheaf_pullback_additive f
  let := abelianSheaf_pullback_preservesFiniteLimits f
  let := closedEmbeddingPushforwardPreservesFiniteColimits hf
  let e := (abelianSheafPullbackConstantIso f).app (AddCommGrpCat.of (ULift.{u} ℤ))
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  change (Abelian.Ext.mk₀ e.inv).comp (adj.extEquiv.symm (x.comp
      (Abelian.Ext.mk₀ ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map φ)) (add_zero n)))
      (zero_add n) =
    ((Abelian.Ext.mk₀ e.inv).comp (adj.extEquiv.symm x) (zero_add n)).comp
      (Abelian.Ext.mk₀ φ) (add_zero n)
  rw [adj.extEquiv_symm_naturality_right₀]
  symm
  apply Abelian.Ext.comp_assoc
  lia

noncomputable def closedEmbeddingCohomologyFunctorIso {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) (n : ℕ) :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙
        Sheaf.functorH.{u} (Opens.grothendieckTopology Y) n ≅
      Sheaf.functorH.{u} (Opens.grothendieckTopology X) n :=
  NatIso.ofComponents
    (fun F ↦ (closedEmbeddingCohomologyAddEquiv hf F n).toAddCommGrpIso)
    (by
      intro F G φ
      ext x
      exact closedEmbeddingCohomologyAddEquiv_naturality hf φ n x)

end MixedFujita
