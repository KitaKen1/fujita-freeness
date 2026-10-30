/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryKlt
public import MixedFujita.SNCWeightLemmaOne

/-!
Quantitative discrepancy comparison for signed SNC boundaries (section 3.1, step 15).

If the integer coefficients of B are smaller than d, their distance from d is at least one.
The actual SNC Jacobian inequality therefore gives

  A_X(E) ≤ d A_(X,B/d)(E)

on every smooth birational model. The bound includes negative coefficients and uses the actual
Cartier pullback and relative canonical divisor. In particular the epsilon in the klt version of
Lemma 1 can be chosen as 1/d on a fixed SNC model, without a separate gap hypothesis.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The integral gap below the boundary denominator compares actual discrepancies on every
smooth birational model. -/
theorem isSNCFamily_relativeCanonical_le_logDiscrepancy
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ))
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T) :
    1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT etaleCharts_cover) (t : T) ≤
      (d : ℤ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T) := by
  obtain ⟨c, σ, hc, hcsnc, hformula⟩ := isSNCFamily_actual_discrepancy_formula ρ hρ
    c₀ f₀ d B ξ hinj hξ hsnc hsupport cT t
  obtain ⟨c', hc'⟩ : ∃ c' : EtaleChart K T n, (t : T) ∈ c'.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := T) (n := n)).symm ▸
      Opens.mem_top (t : T))
  have hK : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT etaleCharts_cover) (t : T) = T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt ρ c₀
      etaleCharts_cover cT etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c₀ cT) (t : T) c hc c' hc'),
      IsUnit.unit_spec]
  have hJ : 0 ≤ T.ord (chartRelativeJacobianDet ρ c c') (t : T) := by
    rw [chartRelativeJacobianDet_eq_stalk ρ (t : T) c hc c' hc']
    exact scheme_ord_nonneg_of_mem_stalk (t : T) _ ⟨_, rfl⟩
  have h := (snc_integer_discrepancy_bound d hd _ hJ _ _
    (fun i => sncChartComponentEquation_pullback_ord_nonneg ρ c σ (t : T) hc i)
    (actual_snc_coordinate_sum_le_jacobian ρ hρ t c hc ξ σ hcsnc c' hc') hb).1
  rw [hK, hformula c' hc']
  nlinarith

/-- The same comparison in the normalized crepant-boundary form used by weight profiles. -/
theorem isSNCFamily_logDiscrepancy_comparison
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ))
    (cT : EtaleChart K T n) (t : CodimensionOnePoint T) :
    (1 : ℝ) + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT etaleCharts_cover) (t : T) ≤
      (d : ℝ) * (((d : ℝ) - cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
        cT etaleCharts_cover) (t : T)) / d) := by
  have h := isSNCFamily_relativeCanonical_le_logDiscrepancy ρ hρ c₀ f₀ d hd B ξ hinj hξ hsnc
    hsupport hb cT t
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg]
  push_cast
  rw [mul_div_cancel₀ _ hd0]
  rw [sub_neg_eq_add]
  exact_mod_cast h

end MixedFujita
