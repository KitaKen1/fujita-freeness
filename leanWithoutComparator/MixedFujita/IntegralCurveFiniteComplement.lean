/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperCurveDegree

/-!
A proper closed subset of a Noetherian integral scheme of dimension at most
one consists of finitely many codimension-one points. Thus every nonempty
open has finite closed complement. A second affine open covering that
complement gives a two-affine cover. The common affine neighborhood property
for finite closed subsets remains an explicit hypothesis.
-/

@[expose] public section
open AlgebraicGeometry Order TopologicalSpace
namespace MixedFujita
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem integralCurve_closedSubset_coheight_eq_one
    (hX : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hproper : Z ≠ Set.univ) (x : X) (hx : x ∈ Z) : coheight x = 1 := by
  have hp : closure Z ≠ Set.univ := by rwa [hZ.closure_eq]
  have hlt : x < (⊤ : X) :=
    QuasiSober.val_lt_genericPoint_of_closure_ne_univ hp ⟨x, hx⟩
  have hdim : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX
  exact le_antisymm hdim (Order.one_le_iff_pos.mpr (coheight_pos_of_lt_top hlt))

variable [IsNoetherian X]

theorem integralCurve_proper_closedSubset_finite
    (hX : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hproper : Z ≠ Set.univ) : Z.Finite := by
  let : QuasiSober ↥Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hp : closure Z ≠ Set.univ := by rwa [hZ.closure_eq]
  have hfin := NoetherianSpace.finite_coheight_one_of_closure_ne_univ hp
  exact hfin.subset fun x hx ↦ ⟨hx,
    integralCurve_closedSubset_coheight_eq_one hX hZ hproper x hx⟩

theorem integralCurve_nonemptyOpen_complement_finite
    (hX : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : (U : Set X).Nonempty) :
    (U : Set X)ᶜ.Finite := by
  apply integralCurve_proper_closedSubset_finite hX U.isOpen.isClosed_compl
  obtain ⟨x, hx⟩ := hU
  intro h
  have hx' : x ∈ (U : Set X)ᶜ := h.symm ▸ Set.mem_univ x
  exact hx' hx

theorem integralCurve_exists_affineOpen_finite_complement
    (hX : topologicalKrullDim X ≤ 1) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (U : Set X).Nonempty ∧ (U : Set X)ᶜ.Finite := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨U, hU, ⟨x, hx⟩, integralCurve_nonemptyOpen_complement_finite hX U ⟨x, hx⟩⟩

theorem integralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods
    (hX : topologicalKrullDim X ≤ 1)
    (hAF : ∀ Z : Set X, Z.Finite → IsClosed Z →
      ∃ V : X.Opens, IsAffineOpen V ∧ Z ⊆ V) :
    ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  classical
  obtain ⟨U, hU, _, hfin⟩ := integralCurve_exists_affineOpen_finite_complement hX
  obtain ⟨V, hV, hsub⟩ := hAF _ hfin U.isOpen.isClosed_compl
  refine ⟨U, V, hU, hV, top_unique fun x _ ↦ ?_⟩
  by_cases hx : x ∈ U
  · exact Or.inl hx
  · exact Or.inr (hsub hx)

end MixedFujita
