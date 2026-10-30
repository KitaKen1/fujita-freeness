/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeneralSNCSectionBaseStrictBound
public import MixedFujita.MarkedSectionBaseSNCSupport

/-! The actual section-base threshold model in every positive dimension.
The original supplied leading-form threshold gives strict inequalities
at every other prime meeting the marked member. Actual supported
point-centre and discrepancy data come from the constructed SNC model;
no local coordinate, formal-map or Jacobian input is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [IsLocallyNoetherian X] [IsProper (X ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 1800000 in
theorem exists_sectionBase_snc_model_with_pointBlowup_threshold
    {J : Type*} [Finite J] [Nonempty J] [DecidableEq K]
    (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n) (x : X) (hx : IsClosed ({x} : Set X))
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (s : J → Γ(M.sheaf, ⊤))
    (hs : ∀ j, s j ≠ 0) (h : ℕ) (hh : 0 < h)
    (horders : ∀ j, cartierSectionVanishingOrder M x (s j) = ((n * h : ℕ) : ℕ∞))
    (fM : X.functionFieldˣ) (hfM : M.IsLocalEquationAt x fM)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hthreshold : ProjectiveThresholdCondition (fun j => homogeneousTaylorForm (n * h)
      (cartierTaylorCoordinates M x fM hfM e (s j))) h) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (.of K))) (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (.of K))) (_ : IsProper (T ↘ Spec (.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (.of K))) (_ : IsProper ρ) (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T) (k₀ : Fin r)
      (G : CartierDivisor T) (hG : G.IsEffective),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (t : T) = 0) ∧
      effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) ∧
      CartierIsGloballyGenerated (cartierPullback ρ M - G) ∧
      ρ (ξ k₀) = x ∧
      cartierCoefficient G (ξ k₀) = (h : ℤ) *
        (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (ξ k₀)) ∧
      ∀ t : CodimensionOnePoint T,
        (closure ({(t : T)} : Set T) ∩ closure ({ξ k₀} : Set T)).Nonempty →
        cartierCoefficient G (t : T) ≤ (h : ℤ) *
          (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
            (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
            cT etaleCharts_cover) (t : T)) ∧
        (cartierCoefficient G (t : T) = (h : ℤ) *
          (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
            (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
            cT etaleCharts_cover) (t : T)) → (t : T) = ξ k₀) := by
  classical
  obtain ⟨T, _, _, _, _, _, ρ, _, _, _, _, hρ, cT, r, ξ, k₀, G, hG,
      hinj, hcoh, hsnc, hTB, _, hGI, hG0, hGG, ⟨E, hE, hEI, hE0, hEe⟩,
      ⟨g, hg, _, _, _⟩, hρx, hGmark, hDmark, heq⟩ :=
    exists_marked_sectionBase_snc_model_with_all_support hn hn1 x hx c₀ M s hs h hh horders
  have hD0 (t : CodimensionOnePoint T) (ht : (t : T) ∉ Set.range ξ) :
      cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT etaleCharts_cover) (t : T) = 0 := by
    have hb := hTB t ht
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, neg_eq_zero,
      add_zero, logDiscrepancyDivisor_boundary_zero, one_smul] at hb
    exact hb
  rw [add_zero, logDiscrepancyDivisor_boundary_zero, one_smul] at hDmark
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ρ, inferInstance, inferInstance, inferInstance, inferInstance, hρ, cT, r, ξ, k₀, G, hG,
    hinj, hcoh, hsnc, hTB, hGI, hG0, hGG, hρx, heq, ?_⟩
  intro t hmeet
  by_cases hte : (t : T) = ξ k₀
  · rw [hte]
    exact ⟨heq.le, fun _ => rfl⟩
  · have hlt : cartierCoefficient G (t : T) < (h : ℤ) *
        (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
          cT etaleCharts_cover) (t : T)) := by
      by_cases ht : (t : T) ∈ Set.range ξ
      · obtain ⟨i, hi⟩ := ht
        have hik : i ≠ k₀ := fun hik => hte (by rw [← hi, hik])
        have hmeet' : (closure ({ξ i} : Set T) ∩ closure ({ξ k₀} : Set T)).Nonempty := by
          simpa only [hi] using hmeet
        have hb := pointBlowup_snc_fixedPart_strict_coefficient hn x hx ρ hρ c₀ cT g hg ξ hinj hcoh hsnc
          k₀ hρx E hE hEI hE0 hEe hD0 hDmark M s hs G hG hGI hG0 h hGmark fM hfM e
            (fun j => (horders j).symm.le) hthreshold i hik hmeet'
        simpa only [hi] using hb
      · rw [hG0 t ht]
        have hcan : 0 ≤ cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀
            etaleCharts_cover cT etaleCharts_cover) (t : T) :=
          cartierCoefficient_nonneg_of_isEffective _
            (birationalRelativeCanonicalDivisor_isEffective ρ hρ c₀ etaleCharts_cover cT etaleCharts_cover) _
        have hhZ : (0 : ℤ) < h := by exact_mod_cast hh
        exact mul_pos hhZ (by omega)
    have hlt' : cartierCoefficient G (t : T) < (h : ℤ) *
        (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (t : T)) := by
      rw [add_zero, logDiscrepancyDivisor_boundary_zero, one_smul]
      exact hlt
    exact ⟨hlt'.le, fun hequal => (ne_of_lt hlt' hequal).elim⟩

end MixedFujita
