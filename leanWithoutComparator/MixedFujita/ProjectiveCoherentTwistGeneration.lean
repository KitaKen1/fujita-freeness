/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveCoherentPresentation
public import MixedFujita.PolynomialHyperplaneSerreVanishing

/-! 実射影Cartier全高次捻りの有限自由全射。 See reports/check-259-ample-ideal-generators-natural-corrections.json for the verified scope. All sufficiently high ORIGINAL ample Cartier twists of any actual coherent module are quotients of finite free sheaves, in every residue class. Actual noninvertible ideal modules are internally coherent and get finite canonical actual global generators. The canonical ideal inclusion pulls back to ZERO on its own actual closed subscheme by the actual adjunction mate. Arbitrary module tensor and NATURAL section restriction preserve this zero; finite ideal corrections preserve exact natural restriction and nonzero restricted sections even for nonreduced closed subschemes. Comparison of the finite ambient Cartier image family with center-exterior basepointfreeness, exterior LC/Bertini, ambient non-LC from restricted concentration, original L nonvanishing, general KV, BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- All high actual hyperplane-Cartier twists of an arbitrary coherent module
are quotients of actual finite free sheaves. The generators and epimorphism
are internal, using SGA generation, projection formula and the actual closed
immersion counit. This is generation, not merely cohomological vanishing. -/
theorem projectivelyEmbedded_cartier_tensor_all_high_finite_free_epi
    {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ}
    [IsIntegral (polynomialProjectiveScheme (r + 1) R)]
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme (r + 1) R) [IsClosedImmersion e]
    (J : CartierDivisor (polynomialProjectiveScheme (r + 1) R)) (H : CartierDivisor X)
    (a : (projectiveSpace.twistingBundle (Fin (r + 1)) R).toModules 1 ≅ J.sheaf)
    (b : (Scheme.Modules.pullback e).obj J.sheaf ≅ H.sheaf)
    (M : X.Modules) [M.IsCoherent] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ (k : ℕ)
      (π : CohomologyAux.unitBiproduct X k ⟶ ((j • H).sheaf ⊗ M)), Epi π := by
  classical
  let L := projectiveSpace.twistingBundle (Fin (r + 1)) R
  let F := (Scheme.Modules.pushforward e).obj M
  have hF := projectiveSpace.IsStdFinite.pushforward e M
  let : F.IsQuasicoherent := hF.isQuasicoherent
  obtain ⟨j₀, hj₀⟩ := projectiveSpace.exists_generating_twist_sections F hF.finite
  refine ⟨j₀, fun j hj => ?_⟩
  obtain ⟨I, _, g, hg⟩ := hj₀ j hj
  let k := Fintype.card I
  let g' : Fin k → Γ(L.twist F j, ⊤) := g ∘ (Fintype.equivFin I).symm
  let φ : CohomologyAux.unitBiproduct _ k ⟶ L.twist F j :=
    biproduct.desc (fun i => CohomologyAux.homOfSection (L.twist F j) (g' i))
  have hφ : Epi φ := by
    apply CohomologyAux.epi_biproduct_desc_homOfSection (L.twist F j) g'
      (projectiveSpace.topStd (Fin (r + 1)) R) projectiveSpace.iSup_topStd
      projectiveSpace.isAffineOpen_topStd
    intro i
    rw [← hg i]
    congr 1
    exact (Fintype.equivFin I).symm.surjective.range_comp
      (fun t => (L.twist F j).presheaf.map (homOfLE le_top :
        projectiveSpace.topStd (Fin (r + 1)) R i ⟶ ⊤).op (g t))
  let := hφ
  let c : L.twist F j ≅ (Scheme.Modules.pushforward e).obj ((j • H).sheaf ⊗ M) :=
    (sgaTwistTensorIso L F j).symm ≪≫
      tensorIso (sgaLineBundleNatPowerCartierIso L J a j) (Iso.refl F) ≪≫
      cartierProjectionFormulaIso (j • J) e M ≪≫
      (Scheme.Modules.pushforward e).mapIso
        (tensorIso (cartierPullbackGradedIso J e H b j) (Iso.refl M))
  let φ' := φ ≫ c.hom
  let : (Scheme.Modules.pullback e).IsLeftAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction e).isLeftAdjoint
  have hmap : Epi ((Scheme.Modules.pullback e).map φ') := (Scheme.Modules.pullback e).map_epi φ'
  let := hmap
  have hc := closedImmersion_module_counit_epi e ((j • H).sheaf ⊗ M)
  let := hc
  exact ⟨k, (modulePullbackUnitBiproductIso e k).inv ≫ (Scheme.Modules.pullback e).map φ' ≫
    (Scheme.Modules.pullbackPushforwardAdjunction e).counit.app ((j • H).sheaf ⊗ M), inferInstance⟩


/-- The finite free generators above apply to the actual hyperplane Cartier
divisor of any integral projective closed subscheme. -/
theorem projectiveHyperplane_tensor_all_high_finite_free_epi
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] {r : ℕ}
    {X : Scheme.{u}} [IsIntegral X]
    (e : X ⟶ polynomialProjectiveScheme (r + 1) R) [IsClosedImmersion e]
    (g : MvPolynomial (Fin (r + 1)) R) (hg : g.IsHomogeneous 1)
    (hgX : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (M : X.Modules) [M.IsCoherent] :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∃ (k : ℕ)
      (π : CohomologyAux.unitBiproduct X k ⟶
        ((j • projectiveHyperplaneCartier e g hg hgX).sheaf ⊗ M)), Epi π := by
  let P := polynomialProjectiveScheme (r + 1) R
  let : IsIntegral P := polynomialProjectiveScheme_isIntegral R (0 : Fin (r + 1))
  have hg0 : g ≠ 0 := by
    intro h
    apply hgX
    rw [h]
    exact (e (genericPoint X)).asHomogeneousIdeal.zero_mem
  have hgP := polynomialProjective_nonzero_avoids_genericPoint (0 : Fin (r + 1)) g hg0
  let J := projectiveHyperplaneCartier (𝟙 P) g hg hgP
  let b : (Scheme.Modules.pullback e).obj J.sheaf ≅
      (projectiveHyperplaneCartier e g hg hgX).sheaf := by
    simpa only [Category.comp_id] using
      projectiveHomogeneousCartierPullbackIso (𝟙 P) e 1 g hg one_pos hgP hgX
  exact projectivelyEmbedded_cartier_tensor_all_high_finite_free_epi e J _
    (polynomialHyperplaneSGAModuleIso g hg hgP).symm b M

end MixedFujita
