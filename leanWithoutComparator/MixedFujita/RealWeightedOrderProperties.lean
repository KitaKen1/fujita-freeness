/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealWeightedMinimization
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
Valuation properties of real-weighted monomial valuations and the passage from natural to real
weights. For nonnegative weights u, v_u(f) is the least u-weight of the support, so
v_u(f + g) ≥ min(v_u(f), v_u(g)), v_u(c f) ≥ v_u(f), v_u(f g) ≥ v_u(f) + v_u(g), units have value 0
and multiplying by a unit does not change v_u. An inequality between two continuous positively
homogeneous functions of the weights that holds at all natural weights holds at all nonnegative
real weights: approximate u by ⌊N u⌋/N. This is the manuscript's "real weights by rational
approximation" for the bounds of Lemma 1, Lemma 2 and §3.1.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries Finset Filter

variable {σ K : Type*} [Field K] [Fintype σ]

theorem realWeightedOrder_nonneg {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) (f : MvPowerSeries σ K) :
    0 ≤ realWeightedOrder u f := by
  by_cases hf : f = 0
  · rw [realWeightedOrder, dite_eq_left hf]
  obtain ⟨β, -, heq⟩ := exists_coeff_realWeightedOrder u hf
  rw [← heq]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hu i) (Nat.cast_nonneg _)

/-- A lower bound for all exponents of the support bounds the value from below. -/
theorem le_realWeightedOrder {u : σ → ℝ} {f : MvPowerSeries σ K} (hf : f ≠ 0) {c : ℝ}
    (h : ∀ β, coeff β f ≠ 0 → c ≤ ∑ i, u i * β i) : c ≤ realWeightedOrder u f := by
  obtain ⟨β, hβ, heq⟩ := exists_coeff_realWeightedOrder u hf
  rw [← heq]
  exact h β hβ

theorem realWeightedOrder_add_ge {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) {f g : MvPowerSeries σ K}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (realWeightedOrder u f) (realWeightedOrder u g) ≤ realWeightedOrder u (f + g) := by
  apply le_realWeightedOrder hfg
  intro β hβ
  rw [map_add] at hβ
  by_cases hβf : coeff β f = 0
  · rw [hβf, zero_add] at hβ
    exact (min_le_right _ _).trans (realWeightedOrder_le hu hg hβ)
  · exact (min_le_left _ _).trans (realWeightedOrder_le hu hf hβf)

theorem realWeightedOrder_smul_ge {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) (c : K)
    {f : MvPowerSeries σ K} (hf : f ≠ 0) (hcf : c • f ≠ 0) :
    realWeightedOrder u f ≤ realWeightedOrder u (c • f) := by
  apply le_realWeightedOrder hcf
  intro β hβ
  rw [map_smul, smul_eq_mul] at hβ
  exact realWeightedOrder_le hu hf (right_ne_zero_of_mul hβ)

theorem realWeightedOrder_mul_ge {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) {f g : MvPowerSeries σ K}
    (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f * g ≠ 0) :
    realWeightedOrder u f + realWeightedOrder u g ≤ realWeightedOrder u (f * g) := by
  classical
  apply le_realWeightedOrder hfg
  intro β hβ
  rw [coeff_mul] at hβ
  obtain ⟨⟨β₁, β₂⟩, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  rw [Finset.mem_antidiagonal] at hmem
  have h1 := realWeightedOrder_le hu hf (left_ne_zero_of_mul hne)
  have h2 := realWeightedOrder_le hu hg (right_ne_zero_of_mul hne)
  have hsum : ∑ i, u i * (β i : ℝ) = ∑ i, u i * (β₁ i : ℝ) + ∑ i, u i * (β₂ i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hmem, Finsupp.add_apply, Nat.cast_add, mul_add]
  rw [hsum]
  linarith

theorem realWeightedOrder_eq_zero_of_isUnit {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i)
    {g : MvPowerSeries σ K} (hg : IsUnit g) : realWeightedOrder u g = 0 := by
  have hc : coeff (0 : σ →₀ ℕ) g ≠ 0 := by
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (isUnit_iff_constantCoeff.mp hg).ne_zero
  have h := realWeightedOrder_le hu hg.ne_zero hc
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, mul_zero, Finset.sum_const_zero] at h
  exact le_antisymm h (realWeightedOrder_nonneg hu g)

theorem realWeightedOrder_unit_mul {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) {g : MvPowerSeries σ K}
    (hg : IsUnit g) (f : MvPowerSeries σ K) : realWeightedOrder u (g * f) = realWeightedOrder u f := by
  by_cases hf : f = 0
  · rw [hf, mul_zero]
  have hgf : g * f ≠ 0 := mul_ne_zero hg.ne_zero hf
  apply le_antisymm
  · obtain ⟨v, rfl⟩ := hg
    have h := realWeightedOrder_mul_ge hu (v⁻¹ : (MvPowerSeries σ K)ˣ).ne_zero hgf
      (by rw [← mul_assoc, Units.inv_mul, one_mul]; exact hf)
    rw [← mul_assoc, Units.inv_mul, one_mul,
      realWeightedOrder_eq_zero_of_isUnit hu (v⁻¹ : (MvPowerSeries σ K)ˣ).isUnit, zero_add] at h
    exact h
  · have h := realWeightedOrder_mul_ge hu hg.ne_zero hf hgf
    rw [realWeightedOrder_eq_zero_of_isUnit hu hg, zero_add] at h
    exact h

omit [Fintype σ] in
/-- Natural to real weights: an inequality between continuous positively homogeneous functions
that holds at all natural weights holds at all nonnegative real weights. -/
theorem le_of_natural_weights {φ ψ : (σ → ℝ) → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφh : ∀ (c : ℝ), 0 ≤ c → ∀ u, φ (c • u) = c * φ u)
    (hψh : ∀ (c : ℝ), 0 ≤ c → ∀ u, ψ (c • u) = c * ψ u)
    (hnat : ∀ w : σ → ℕ, φ (fun i => (w i : ℝ)) ≤ ψ (fun i => (w i : ℝ)))
    {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) : φ u ≤ ψ u := by
  set w : ℕ → σ → ℝ := fun N i => (⌊(N : ℝ) * u i⌋₊ : ℝ) / N with hw
  have hlim : Tendsto w atTop (nhds u) := by
    rw [tendsto_pi_nhds]
    intro i
    have h := (tendsto_nat_floor_mul_div_atTop (hu i)).comp tendsto_natCast_atTop_atTop
    refine h.congr' ?_
    filter_upwards with N
    simp only [Function.comp, hw, mul_comm]
  have hle : ∀ᶠ N : ℕ in atTop, φ (w N) ≤ ψ (w N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hwN : w N = (1 / (N : ℝ)) • (fun i => ((⌊(N : ℝ) * u i⌋₊ : ℕ) : ℝ)) := by
      funext i
      simp only [hw, Pi.smul_apply, smul_eq_mul]
      field_simp
    rw [hwN, hφh _ (by positivity), hψh _ (by positivity)]
    exact mul_le_mul_of_nonneg_left (hnat fun i => ⌊(N : ℝ) * u i⌋₊) (by positivity)
  exact le_of_tendsto_of_tendsto ((hφ.tendsto u).comp hlim) ((hψ.tendsto u).comp hlim) hle

end MixedFujita
