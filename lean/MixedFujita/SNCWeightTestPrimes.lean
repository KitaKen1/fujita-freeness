/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationWeightMinimizer
public import MixedFujita.ToricExtractionPrime
public import MixedFujita.CrepantDiscrepancyComposition

/-!
Rational weights on a simple normal crossing model are scaled prime divisors over the base, and
the infimum of the objective over the weights does not depend on the model (step 11, sections 1
and 3.2 of the manuscript: the tests are the real-weight monomial valuations, and the positive
rational ones are positive multiples of divisorial valuations).

Let π : X → Y be a birational simple normal crossing model of a pair on Y, with family ξ_k, crepant
boundary B_X supported on the family, and let W ≠ 0 be natural weights on the members through a
point y of X. The toric extraction of the monomial valuation with weights W, composed with π, is a
smooth birational test model σ : U → Y with a prime divisor e whose centre contains π(y), and a
natural number g ≥ 1 such that, for every Cartier divisor G of Y whose pullback to X is supported
on the family,

  g · ord_e(σ*G) = Σ_k ord_{ξ_k}(π*G) W_k,   g · d · A(e) = Σ_k (d − ord_{ξ_k}(B_X)) W_k,

where d · A(e) = d + (coefficient of the discrepancy divisor of the pair at e). So the objective of
the rational weight W/M is the objective of the prime divisor e scaled by g/M, exactly.

Consequence. For two simple normal crossing models of the same pair and the same divisors, the
second one proper, and every weight w over the fibre of x on the first one, the second one has
weights over the fibre of x with objective below objective(w) + ε for every ε > 0: approximate w
by a rational weight with the same support, pass to the prime divisor, and retract it to the
second model. The infimum of the objective over the weights over the fibre of x is the same on all
proper simple normal crossing models; it is the infimum over the scaled prime divisors of the
smooth birational test models whose centre contains x.
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Extraction

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Natural weights on the members of a simple normal crossing model through a point y are a
multiple of a prime divisor over the base: a smooth birational test model σ : U → Y with a prime
divisor e whose centre contains π(y) and g ≥ 1 such that g ord_e(σ*G) = Σ_k ord_{ξ_k}(π*G) W_k for
the divisors G of Y whose pullback is supported on the family, and g times the log discrepancy of
e for the pair (with the denominator d cleared) is Σ_k (d − ord_{ξ_k}(B_X)) W_k. -/
theorem exists_base_test_prime_of_natural_weights {r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (y : X) (W : Fin r → ℕ) (hW : W ≠ 0)
    (hWy : ∀ k, W k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (g : ℕ),
      1 ≤ g ∧ π y ∈ closure ({σ (e : U)} : Set Y) ∧
      (∀ G : CartierDivisor Y, (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π G) (z : X) = 0) →
        (g : ℤ) * cartierCoefficient (cartierPullback σ G) (e : U) =
          ∑ k, cartierCoefficient (cartierPullback π G) (ξ k) * (W k : ℤ)) ∧
      (g : ℤ) * ((d : ℤ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) =
        ∑ k, ((d : ℤ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) * (W k : ℤ) := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, W', hg, hgW, hye, hpull, hdisc⟩ :=
    exists_snc_extraction_prime ξ hinj hξ hsnc y W hW hWy
  refine ⟨U, hUi, hUn, hUo, hUs, σ ≫ π, inferInstance, inferInstance,
    dominantFunctionFieldAlgHom_comp_bijective π σ hπ hσ, cU, e, g, hg, ?_, ?_, ?_⟩
  · have hsp : σ (e : U) ⤳ y := specializes_iff_mem_closure.mpr hye
    exact specializes_iff_mem_closure.mp (hsp.map π.continuous)
  · intro G hG
    rw [cartierPullback_comp, hpull _ hG, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hgW k]
    push_cast
    ring
  · have h := hdisc cX (crepantPullbackFormUnit π hπ cY fY cX) d
      (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) hBsupp
    rw [crepantBoundaryCartier_smooth_recombine π hπ cY fY d D cX] at h
    have hsum : ∑ k, ((d : ℤ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) * (W k : ℤ) =
        (g : ℤ) * ((d : ℤ) * ∑ k, (W' k : ℤ) - ∑ k, cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k) * (W' k : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hgW k]
      push_cast
      ring
    rw [hsum, ← h, logDiscrepancyDivisor_comp π σ hπ hσ cY fY d D cX cU etaleCharts_cover]

/-- The objective of a rational weight W/M on a simple normal crossing model is the objective of a
scaled prime divisor of a smooth birational test model of the base whose centre contains the
image of the point through which the weighted members pass. -/
theorem exists_base_test_prime_objective_eq {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (G : Fin N → CartierDivisor Y)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (G i)) (z : X) = 0)
    (y : X) (W : Fin r → ℕ) (hW : W ≠ 0)
    (hWy : ∀ k, W k ≠ 0 → y ∈ closure ({ξ k} : Set X)) (M : ℕ) (hM : 1 ≤ M) (τ j : ℝ) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (lam : ℝ),
      0 ≤ lam ∧ π y ∈ closure ({σ (e : U)} : Set Y) ∧
      ∑ i, Real.exp (lam * (((d : ℝ) + cartierCoefficient
            (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) / d) / τ -
          lam * (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ) / j) =
        weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j
          (fun k => (W k : ℝ) / M) := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, hg, hcl, hpull, hdisc⟩ :=
    exists_base_test_prime_of_natural_weights π hπ cY fY d D cX ξ hinj hξ hsnc hBsupp y W hW hWy
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, (g : ℝ) / M, by positivity, hcl, ?_⟩
  unfold weightExponentialObjective
  refine Finset.sum_congr rfl fun i _ => ?_
  have hA : (g : ℝ) * ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) =
      ∑ k, ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) * (W k : ℝ) := by
    exact_mod_cast hdisc
  have hv : (g : ℝ) * (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ) =
      ∑ k, (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) * (W k : ℝ) := by
    exact_mod_cast hpull (G i) (hGsupp i)
  have h1 : (g : ℝ) / M * (((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) / d) =
      ∑ k, (W k : ℝ) / M * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d) := by
    have h : ∑ k, (W k : ℝ) / M * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d) =
        (∑ k, ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) * (W k : ℝ)) /
          (M * d) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [h, ← hA]
    field_simp
  have h2 : (g : ℝ) / M * (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ) =
      ∑ k, (W k : ℝ) / M * (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) := by
    have h : ∑ k, (W k : ℝ) / M * (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) =
        (∑ k, (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) * (W k : ℝ)) / M := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [h, ← hv]
    field_simp
  rw [h1, h2]

end Extraction

section Models

variable {K : Type u} [Field K] {n : ℕ} {Y X X' : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X] [IsIntegral X']
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [X'.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X] [IsLocallyNoetherian X']
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X' ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (π' : X' ⟶ Y) [IsDominant π'] [π'.IsOver (Spec (CommRingCat.of K))] [IsProper π']
  (hπ' : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π'))

/-- The infimum of the objective over the weights over the fibre of x does not depend on the
simple normal crossing model: for two models of the same pair and the same divisors, the second
one proper, every weight over the fibre of x on the first one and every ε > 0, some weight over the
fibre of x on the second one has objective smaller than the objective of the given weight plus
ε. -/
theorem exists_sncWeight_objective_lt_of_model {N r r' : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (G : Fin N → CartierDivisor Y)
    (cX : EtaleChart K X n) (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (G i)) (z : X) = 0)
    (cX' : EtaleChart K X' n) (ξ' : Fin r' → X') (hinj' : Function.Injective ξ')
    (hξ' : ∀ i, Order.coheight (ξ' i) = 1) (hsnc' : IsSNCFamily K n ξ')
    (hBsupp' : ∀ z : CodimensionOnePoint X', (z : X') ∉ Set.range ξ' →
      cartierCoefficient (crepantBoundaryCartier π' hπ' cY fY d D cX' etaleCharts_cover)
        (z : X') = 0)
    (hGsupp' : ∀ i, ∀ z : CodimensionOnePoint X', (z : X') ∉ Set.range ξ' →
      cartierCoefficient (cartierPullback π' (G i)) (z : X') = 0)
    (x : Y) (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k)
    (hwΦ : ∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    {τ : ℝ} (hτ : 0 < τ) (j : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w' : Fin r' → ℝ, (∀ k, 0 ≤ w' k) ∧
      (∃ p ∈ π' ⁻¹' ({x} : Set Y), ∀ k, w' k ≠ 0 → p ∈ closure ({ξ' k} : Set X')) ∧
      weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π' hπ' cY fY d D cX' etaleCharts_cover) (ξ' k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π' (G i)) (ξ' k) : ℝ)) τ j w' <
        weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j w + ε := by
  obtain ⟨p, hpx, hwp⟩ := hwΦ
  have hcont : Continuous (weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j) := by
    unfold weightExponentialObjective
    fun_prop
  obtain ⟨η, hη, hclose⟩ := Metric.continuous_iff.mp hcont w ε hε
  -- a rational weight with the same support, close to w
  have hq : ∀ k, ∃ q : ℚ, 0 ≤ q ∧ dist (q : ℝ) (w k) < η ∧ (w k = 0 → q = 0) := by
    intro k
    by_cases hk : w k = 0
    · refine ⟨0, le_rfl, ?_, fun _ => rfl⟩
      rw [hk, Rat.cast_zero, dist_self]
      exact hη
    · have hpos : 0 < w k := lt_of_le_of_ne (hw0 k) (Ne.symm hk)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show w k < w k + η by linarith)
      refine ⟨q, ?_, ?_, fun h => absurd h hk⟩
      · exact_mod_cast (hpos.trans hq1).le
      · rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
  choose q hq0 hqd hqz using hq
  obtain ⟨M, W, hM, hWq⟩ := exists_common_denominator_nat q hq0
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hwq : (fun k => (W k : ℝ) / M) = fun k => (q k : ℝ) := by
    funext k
    have h : (W k : ℝ) = (M : ℝ) * (q k : ℝ) := by exact_mod_cast hWq k
    rw [h]
    field_simp
  have hobj : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j
        (fun k => (W k : ℝ) / M) <
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j w + ε := by
    have hdist : dist (fun k => (W k : ℝ) / M) w < η := by
      rw [hwq, dist_pi_lt_iff hη]
      exact hqd
    have h := hclose _ hdist
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.2]
  by_cases hW : W = 0
  · -- the zero weight: both objectives are N
    obtain ⟨p', hp'⟩ := surjective_of_isProper_of_isDominant π' x
    refine ⟨fun _ => 0, fun _ => le_rfl, ⟨p', hp', fun k hk => absurd rfl hk⟩, ?_⟩
    have h0 : (fun k => (W k : ℝ) / M) = fun _ => (0 : ℝ) := by
      funext k
      rw [hW]
      simp
    rw [h0] at hobj
    have e1 : ∀ {s : ℕ} (a : Fin s → ℝ) (e : Fin N → Fin s → ℝ),
        weightExponentialObjective a e τ j (fun _ => (0 : ℝ)) = N := by
      intro s a e
      simp [weightExponentialObjective]
    rw [e1] at hobj ⊢
    exact hobj
  · have hWy : ∀ k, W k ≠ 0 → p ∈ closure ({ξ k} : Set X) := fun k hk => hwp k fun h0 => hk (by
      have h := hWq k
      rw [hqz k h0, mul_zero] at h
      exact_mod_cast h)
    obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, lam, hlam, hcl, heq⟩ :=
      exists_base_test_prime_objective_eq π hπ cY fY d hd D cX ξ hinj hξ hsnc hBsupp G hGsupp p W
        hW hWy M hM τ j
    have hpx' : π p = x := hpx
    obtain ⟨w', hw'0, hw'Φ, hle⟩ := exists_sncWeight_objective_le_of_test_prime π' hπ' cY fY d hd
      D cX' ξ' hinj' hξ' hsnc' hBsupp' G hGsupp' σ hσ cU e x (by rw [← hpx']; exact hcl) hτ j lam
      hlam
    exact ⟨w', hw'0, hw'Φ, lt_of_le_of_lt (hle.trans heq.le) hobj⟩

end Models

end MixedFujita
