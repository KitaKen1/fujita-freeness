/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RoundupBoundaryNormalization
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.ExceptionalCartierPushforwardIso
public import MixedFujita.ExceptionalCartierSections

/-!
After normalization on the source, the difference between a higher actual
crepant roundup and the pullback of the source roundup is effective and
exceptional. Its actual canonical direct-image unit map is an isomorphism.
No SNC support of the normalized boundary on the higher model is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The actual difference roundup has exactly the normalized pair's coefficients. -/
theorem crepant_roundup_difference_coefficient
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor X) (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (t : CodimensionOnePoint T) :
    cartierCoefficient (E₁ - cartierPullback ρ E₀) (t : T) =
      ⌈-((cartierCoefficient
        (crepantBoundaryCartier ρ hρ c f d (D + d • E₀) cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉ := by
  rw [cartierCoefficient_sub, hE₁ t, crepantBoundaryCartier_add_source,
    cartierPullback_nsmul, cartierCoefficient_add, cartierCoefficient_nsmul]
  exact (boundary_roundup_add_integral_coefficient
    (cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T))
    (cartierCoefficient (cartierPullback ρ E₀) (t : T)) d hd).symm

/-- An effective klt normalization makes the actual higher-roundup difference
effective exceptional, and its actual canonical direct-image map an isomorphism. -/
theorem crepant_roundup_difference_effective_exceptional_unit_iso
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d (D + d • E₀))
    (hklt : LogPairIsKlt c f d (D + d • E₀))
    (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) :
    ∃ hC : (E₁ - cartierPullback ρ E₀).IsEffective,
      (∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
        cartierCoefficient (E₁ - cartierPullback ρ E₀) (t : T) = 0) ∧
      IsIso (effectiveCartierPushforwardUnitMap ρ (E₁ - cartierPullback ρ E₀) hC) := by
  have hc := crepant_roundup_difference_coefficient ρ hρ c f d hd D E₀ cT E₁ hE₁
  have hb (t : CodimensionOnePoint T) :=
    logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d (D + d • E₀) hklt cT t
  have hC : (E₁ - cartierPullback ρ E₀).IsEffective := by
    apply (normal_cartier_isEffective_iff_coefficients_nonneg hnormT _).mpr
    intro t
    rw [hc t, Int.ceil_neg]
    exact negative_floor_normalized_coefficient_nonneg _ d hd (hb t)
  have hEx : ∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
      cartierCoefficient (E₁ - cartierPullback ρ E₀) (t : T) = 0 := by
    intro t ht
    have hlo := crepantBoundary_coefficient_nonneg_over_normal_prime ρ hρ hnormX hcov
      c f d (D + d • E₀) heff cT t ht
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have h0 : (0 : ℝ) ≤
        (cartierCoefficient (crepantBoundaryCartier ρ hρ c f d (D + d • E₀)
          cT etaleCharts_cover) (t : T) : ℝ) / d :=
      div_nonneg (by exact_mod_cast hlo) hdR.le
    have h1 :
        (cartierCoefficient (crepantBoundaryCartier ρ hρ c f d (D + d • E₀)
          cT etaleCharts_cover) (t : T) : ℝ) / d < 1 :=
      (div_lt_one hdR).mpr (by exact_mod_cast hb t)
    rw [hc t, Int.ceil_neg, Int.floor_eq_zero_iff.mpr ⟨h0, h1⟩, neg_zero]
  exact ⟨hC, hEx, effectiveExceptionalCartierPushforwardUnitMap_isIso
    hnormX hnormT ρ hρ (E₁ - cartierPullback ρ E₀) hC hEx⟩

/-- The actual rational section lattices of the original roundups agree on
every nonempty source open after the same proper crepant refinement. -/
theorem crepant_roundup_mem_sections_iff_on_open
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d (D + d • E₀))
    (hklt : LogPairIsKlt c f d (D + d • E₀))
    (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (U : X.Opens) [Nonempty U] (z : X.functionField) :
    letI := dominant_preimage_nonempty ρ U
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom z) ∈ E₁.sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := X) U).symm z ∈ E₀.sections U := by
  letI := dominant_preimage_nonempty ρ U
  obtain ⟨hC, hEx, -⟩ := crepant_roundup_difference_effective_exceptional_unit_iso
    ρ hρ hnormX hnormT hcov c f d hd D E₀ heff hklt cT E₁ hE₁
  have h := mem_sections_effective_exceptional_cartierPullback_iff_on_open
    hnormX hnormT ρ hρ (E₁ - cartierPullback ρ E₀) hC hEx E₀ U z
  simpa only [add_sub_cancel] using h

end MixedFujita
