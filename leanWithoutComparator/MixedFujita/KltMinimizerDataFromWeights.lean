/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltNumericalFreenessConditional
public import MixedFujita.IsolationWeightMinimizer
public import MixedFujita.CartierSectionPullbackAvoidance

/-!
The data of the minimizer at a closed point of a klt pair from a fixed family of sections
(steps 11 and 15).

Let s_1, …, s_N be nonzero sections of j L on a klt pair, one of which does not vanish at the
closed point x, and π : X → Y a smooth proper simple normal crossing model supporting the crepant
boundary and the pullbacks of the zero divisors. For t > 0 with d t < 1, suppose

* (interior condition) some weight over π⁻¹(x) on the family has exponential objective smaller
  than N;
* (point centres) for every nonzero minimizer w of the objective over π⁻¹(x), a point p of X
  whose closure meets π⁻¹(x) and whose polytope contains the profile of w lies in π⁻¹(x).

Then the data of the minimizer at x exist (`KltIsolationMinimizerData`): the minimizer exists by
coercivity, its first-order conditions give c, q, the polytope membership and the inequality
(24), and the budget is d j Σ c_i = d t < 1.

What remains for the statements on the existence of the data of the minimizer is therefore the
choice of the degree and of the sections for which the interior condition and the point-centre
property hold (sections 2, 5, 7 and 8 of the manuscript).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]

omit [IsLocallyNoetherian Y] in
/-- The data of the minimizer at the closed point x from a fixed family of sections of j L on its
simple normal crossing model: one section does not vanish at x, d t < 1, some weight over π⁻¹(x)
has objective smaller than N, and the profiles of the nonzero minimizers have the point-centre
property. -/
theorem kltIsolationMinimizerData_of_sncWeight_minimizer
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D) (L : CartierDivisor Y) (m₀ : ℕ) (x : Y)
    (j : ℕ) (hj : 1 ≤ j) (hjm₀ : m₀ ∣ j) {N : ℕ} (hN : 0 < N)
    (s : Fin N → Γ((j • L).sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) (i₀ : Fin N)
    (hi₀ : x ∈ cartierSectionNonvanishingOpen (j • L) (s i₀))
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (z : X) = 0)
    {t : ℝ} (ht : 0 < t) (hdt : (d : ℝ) * t < 1)
    (w₁ : Fin r → ℝ) (hw₁0 : ∀ k, 0 ≤ w₁ k)
    (hw₁Φ : ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w₁ k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    (hint : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w₁ < N)
    (hpc : ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
      (∃ k, w k ≠ 0) →
      (∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w' k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
        weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w') →
      ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
        InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
          (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
          (fun i => (∑ k, w k * (cartierCoefficient (cartierPullback π
              (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) /
            ∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)) p →
        p ∈ π ⁻¹' ({x} : Set Y)) :
    KltIsolationMinimizerData cY fY d D L m₀ x := by
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D hklt cX ⟨ξ k, hξ k⟩
  -- the section which does not vanish at x has zero coefficients along the members over x
  have hi₀' : ∀ k, (closure ({ξ k} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i₀) (hs i₀))) (ξ k) = 0 := by
    rintro k ⟨p, hpk, hpx⟩
    refine cartierPullback_sectionZeroDivisor_coefficient_zero_of_avoided π (j • L) (s i₀) (hs i₀)
      ⟨ξ k, hξ k⟩ ?_
    have hpx' : π p = x := hpx
    have hspec : π (ξ k) ⤳ π p := (specializes_iff_mem_closure.mpr hpk).map π.continuous
    have hmem : π (ξ k) ∈ cartierSectionNonvanishingOpen (j • L) (s i₀) :=
      hspec.mem_open (cartierSectionNonvanishingOpen (j • L) (s i₀)).isOpen (by rw [hpx']; exact hi₀)
    exact fun h => h hmem
  obtain ⟨w, hw0, ⟨y, hy, hwy⟩, hwne, hwmin⟩ := exists_sncWeight_minimizer ξ d hd _ hb
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
    (π ⁻¹' ({x} : Set Y)) ht (j : ℝ) i₀ hi₀' w₁ hw₁0 hw₁Φ hint
  obtain ⟨hc, hcq, hqy, hpoly, hsum⟩ := isolation_data_of_sncWeight_minimizer hN ξ d hd _ hb
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
    (π ⁻¹' ({x} : Set Y)) ht j hj w hw0 y hy hwy hwne hwmin
  have hcentre := hpc w hw0 ⟨y, hy, hwy⟩ hwne hwmin
  refine ⟨j, N, s, hs, X, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    π, inferInstance, inferInstance, inferInstance, hπ, cX, r, ξ, y, _, _, hjm₀, hinj, hξ, hsnc,
    hBsupp, hDsupp, hy, hc, hcq, hqy, hpoly, hcentre, ?_⟩
  have hcast : ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) := by push_cast; ring
  rw [hcast, mul_assoc, hsum]
  exact hdt

end MixedFujita
