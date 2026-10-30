/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANegativeTwistMonomorphisms
public import MixedFujita.CartierNegativeSGAPowers
public import MixedFujita.ProperCartierCohomology
public import MixedFujita.ModuleGlobalSectionsFiniteSums

/-! 任意proper非被約源の全負Cartier捻りの切断数上界。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Every negative pulled Cartier twist injects into the original pulled
coefficient on an arbitrary noetherian source, if the subtracted ambient
Cartier line is globally generated. All actual maps are internal. -/
theorem cartierPulledNegativeTwist_exists_mono
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsNoetherian Y]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (E : CartierDivisor X) (j : ℕ) :
    ∃ f : (Scheme.Modules.pullback p).obj (E - j • H).sheaf ⟶
      (Scheme.Modules.pullback p).obj E.sheaf, Mono f := by
  obtain ⟨f, hf⟩ := cartier_sga_pullback_exists_mono_negative_twist K p H hH
    ((cartierSGALineBundle E).pullback p) 1 j
  let := hf
  exact ⟨(cartierPulledNegativeSGATwistIso p E H j).hom ≫ f ≫
    (cartierPulledSheafSGAPowerOneIso E p).hom, inferInstance⟩


/-- On a proper possibly nonreduced source, subtracting ANY natural
multiple of a generated ambient Cartier line never increases the actual
dimension of the pulled coefficient's global sections. -/
theorem proper_cartierPulled_negative_twist_sections_le
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (E : CartierDivisor X) (j : ℕ) :
    Module.finrank K Γ((Scheme.Modules.pullback p).obj (E - j • H).sheaf, ⊤) ≤
      Module.finrank K Γ((Scheme.Modules.pullback p).obj E.sheaf, ⊤) := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let M := (Scheme.Modules.pullback p).obj E.sheaf
  let : SheafOfModules.isInvertible Y M := cartierPullbackSheaf_isInvertible E p
  let : M.IsCoherent := invertible_module_isCoherent M
  let : FiniteDimensional K (Scheme.Modules.Cohomology M 0) := proper_coherent_cohomology_finite K M 0
  let a := Scheme.Modules.cohomologyZeroBaseLinearEquiv K Y M
  let : FiniteDimensional K Γ(M, ⊤) := FiniteDimensional.of_injective a.symm.toLinearMap a.symm.injective
  obtain ⟨f, hf⟩ := cartierPulledNegativeTwist_exists_mono K p H hH E j
  let := hf
  exact LinearMap.finrank_le_finrank_of_injective
    (f := moduleHomGlobalSectionsBaseLinearMap K f) (CohomologyAux.app_injective_of_mono f ⊤)

end MixedFujita
