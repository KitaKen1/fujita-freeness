/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.Zero

/-!
Pushforward of abelian sheaves along a closed topological embedding is exact.
Relative open neighborhoods lift at image points; outside the closed image,
the inverse image of a small open neighborhood is empty and its section group
is zero. This constructs local lifts and proves preservation of epimorphisms.
No proper-cohomology finiteness or dimension bound is assumed or claimed.
-/

@[expose] public section
open CategoryTheory Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X Y : TopCat.{u}} {f : X ⟶ Y}

theorem inducing_relative_open_lift (hf : Topology.IsInducing f)
    (U : Opens Y) (V : Opens X) (hV : V ≤ (Opens.map f).obj U) :
    ∃ W : Opens Y, W ≤ U ∧ (Opens.map f).obj W = V := by
  obtain ⟨A, hA, heq⟩ := hf.isOpen_iff.mp V.isOpen
  refine ⟨U ⊓ ⟨A, hA⟩, inf_le_left, ?_⟩
  ext x
  change (f x ∈ U ∧ f x ∈ A) ↔ x ∈ V
  have hx : f x ∈ A ↔ x ∈ V := by
    exact Set.ext_iff.mp heq x
  exact ⟨fun h ↦ hx.mp h.2, fun h ↦ ⟨hV h, hx.mpr h⟩⟩

theorem closedEmbedding_open_off_image (hf : Topology.IsClosedEmbedding f)
    (U : Opens Y) (x : Y) (hx : x ∈ U) (hxf : x ∉ Set.range f) :
    ∃ W : Opens Y, W ≤ U ∧ x ∈ W ∧ (Opens.map f).obj W = ⊥ := by
  refine ⟨U ⊓ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩,
    inf_le_left, ⟨hx, hxf⟩, ?_⟩
  ext y
  change (f y ∈ U ∧ f y ∉ Set.range f) ↔ False
  simp

theorem abelianSheaf_empty_sections_subsingleton (F : X.Sheaf AddCommGrpCat.{u})
    {U : Opens X} (hU : U = ⊥) : Subsingleton (F.obj.obj (op U)) := by
  let e := (F.isTerminalOfEqEmpty hU).uniqueUpToIso
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit.{u + 1})).isTerminal
  exact e.addCommGroupIsoToAddEquiv.subsingleton

theorem closedEmbedding_pushforward_locallySurjective
    (hf : Topology.IsClosedEmbedding f) {F G : X.Sheaf AddCommGrpCat.{u}}
    (φ : F ⟶ G) (hφ : TopCat.Presheaf.IsLocallySurjective φ.hom) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map φ).hom := by
  rw [TopCat.Presheaf.isLocallySurjective_iff] at hφ ⊢
  intro U t x hx
  by_cases hxf : x ∈ Set.range f
  · obtain ⟨y, rfl⟩ := hxf
    obtain ⟨V, hVU, ⟨s, hs⟩, hy⟩ := hφ ((Opens.map f).obj U) t y hx
    change φ.hom.app (op V) s = G.obj.map (homOfLE hVU).op t at hs
    obtain ⟨W, hWU, hW⟩ := inducing_relative_open_lift hf.isInducing U V hVU
    refine ⟨W, hWU, ?_, ?_⟩
    · refine ⟨F.obj.map (eqToHom hW).op s, ?_⟩
      change φ.hom.app (op ((Opens.map f).obj W))
        (F.obj.map (eqToHom hW).op s) =
          G.obj.map ((Opens.map f).map (homOfLE hWU)).op t
      rw [← ConcreteCategory.comp_apply, φ.hom.naturality]
      rw [ConcreteCategory.comp_apply, hs, ← ConcreteCategory.comp_apply, ← G.obj.map_comp]
      congr 1
    · change y ∈ (Opens.map f).obj W
      simpa only [hW] using hy
  · obtain ⟨W, hWU, hxW, hW⟩ := closedEmbedding_open_off_image hf U x hx hxf
    refine ⟨W, hWU, ⟨0, ?_⟩, hxW⟩
    change φ.hom.app (op ((Opens.map f).obj W)) 0 =
      G.obj.map ((Opens.map f).map (homOfLE hWU)).op t
    let := abelianSheaf_empty_sections_subsingleton G hW
    exact Subsingleton.elim _ _

theorem closedEmbedding_pushforward_epi
    (hf : Topology.IsClosedEmbedding f) {F G : X.Sheaf AddCommGrpCat.{u}}
    (φ : F ⟶ G) [Epi φ] :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map φ) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  exact closedEmbedding_pushforward_locallySurjective hf φ
    ((TopCat.Sheaf.isLocallySurjective_iff_epi φ).mpr inferInstance)

theorem closedEmbeddingPushforwardPreservesEpis
    (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms where
  preserves φ _ := closedEmbedding_pushforward_epi hf φ

theorem abelianSheaf_pushforward_additive (f : X ⟶ Y) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

theorem closedEmbeddingPushforwardPreservesHomology
    (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology := by
  let := closedEmbeddingPushforwardPreservesEpis hf
  let := abelianSheaf_pushforward_additive f
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

theorem closedEmbeddingPushforwardPreservesFiniteColimits
    (hf : Topology.IsClosedEmbedding f) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  let := closedEmbeddingPushforwardPreservesHomology hf
  let := abelianSheaf_pushforward_additive f
  exact Functor.preservesFiniteColimits_of_preservesHomology _

theorem closedEmbedding_pushforward_shortExact
    (hf : Topology.IsClosedEmbedding f)
    (S : ShortComplex (X.Sheaf AddCommGrpCat.{u})) (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)).ShortExact := by
  let := closedEmbeddingPushforwardPreservesHomology hf
  let := closedEmbeddingPushforwardPreservesEpis hf
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map _

end MixedFujita
