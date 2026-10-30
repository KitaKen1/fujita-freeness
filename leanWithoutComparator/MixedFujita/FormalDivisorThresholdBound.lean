/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateDivisorFormalMap
public import MixedFujita.ProjectiveChartThreshold

/-! The all-formal-test projective threshold gives the strict divisor
restriction bound in every dimension. The Jacobian restriction identity
derives the divisor test's nondegeneracy. Restoring the exceptional power
then gives the coefficient inequality from finite SNC order data.
Constructing these formal restriction data on the actual general-
dimensional SNC model remains a separate geometric obligation. -/

@[expose] public section
open MvPowerSeries
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

theorem powerSeriesAlgHom_variable_ne_zero_of_jacobian
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (i : σ) : ψ (X i) ≠ 0 := by
  intro hi
  apply hJ
  apply Matrix.det_eq_zero_of_row_eq_zero i
  intro j
  change pderiv j (ψ (X i)) = 0
  rw [hi, map_zero]

theorem powerSeriesDivisorMap_jacobian_ne_zero
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (k : σ)
    (v : MvPowerSeries σ K) (hnormal : ψ (X k) = X k * v)
    (hJ : powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det ≠ 0) :
    (powerSeriesJacobian (powerSeriesDivisorMap ψ k)).det ≠ 0 := by
  intro hz
  apply hJ
  rw [powerSeriesDivisorRestriction_jacobian_det ψ k v hnormal, hz, mul_zero]

variable {n : ℕ} {J : Type*} [DecidableEq K]

theorem projectiveThreshold_divisor_strict_weighted_bound
    (ψ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) (k : Fin n)
    (v : MvPowerSeries (Fin n) K) (hnormal : ψ (X k) = X k * v)
    (hJ : powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det ≠ 0)
    (p : {i : Fin n // i ≠ k} → K) (f : J → MvPowerSeries (Fin n) K)
    (g : J → MvPolynomial (Fin n) K) (h : ℕ) (hthreshold : ProjectiveThresholdCondition g h)
    (hres : ∀ j, powerSeriesDivisorRestriction k (f j) =
      powerSeriesDivisorMap ψ k (chartShiftedForm k p (g j)))
    (w : {i : Fin n // i ≠ k} → ℕ) (hw : w ≠ 0) :
    ∃ j, (h : ℕ∞) * (powerSeriesDivisorRestriction k v).weightedOrder w +
        (powerSeriesDivisorRestriction k (f j)).weightedOrder w <
      (h : ℕ∞) * (((∑ i, w i : ℕ) : ℕ∞) +
        (powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det).weightedOrder w) := by
  have hJE := powerSeriesDivisorMap_jacobian_ne_zero ψ k v hnormal hJ
  obtain ⟨j, hj⟩ := hthreshold k p (powerSeriesDivisorMap ψ k)
    (powerSeriesAlgHom_variable_ne_zero_of_jacobian _ hJE) hJE w hw
  have hv : powerSeriesDivisorRestriction k v ≠ 0 := by
    intro hz
    apply hJ
    rw [powerSeriesDivisorRestriction_jacobian_det ψ k v hnormal, hz, zero_mul]
  have hfin : (powerSeriesDivisorRestriction k v).weightedOrder w ≠ ⊤ := by
    simpa only [ne_eq, weightedOrder_eq_top_iff] using hv
  obtain ⟨U, hU⟩ := ENat.ne_top_iff_exists.mp hfin
  have hhfin : (h : ℕ∞) * (powerSeriesDivisorRestriction k v).weightedOrder w ≠ ⊤ := by
    rw [← hU, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  refine ⟨j, ?_⟩
  rw [hres j, powerSeriesDivisorRestriction_jacobian_det ψ k v hnormal, weightedOrder_mul]
  calc
    _ < (h : ℕ∞) * (powerSeriesDivisorRestriction k v).weightedOrder w +
        (h : ℕ∞) * (((∑ i, w i : ℕ) : ℕ∞) +
          (powerSeriesJacobian (powerSeriesDivisorMap ψ k)).det.weightedOrder w) :=
      ENat.add_lt_add_of_le_of_lt hhfin le_rfl hj
    _ = _ := by ring

theorem projectiveThreshold_divisor_fixed_coefficient_lt
    (ψ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K) (k : Fin n)
    (v : MvPowerSeries (Fin n) K) (hnormal : ψ (X k) = X k * v)
    (hJ : powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det ≠ 0)
    (p : {i : Fin n // i ≠ k} → K) (f : J → MvPowerSeries (Fin n) K)
    (g : J → MvPolynomial (Fin n) K) (h : ℕ) (hthreshold : ProjectiveThresholdCondition g h)
    (hres : ∀ j, powerSeriesDivisorRestriction k (f j) =
      powerSeriesDivisorMap ψ k (chartShiftedForm k p (g j)))
    (w : {i : Fin n // i ≠ k} → ℕ) (hwsum : ∑ i, w i = 1)
    (b d μ : ℕ)
    (hb : (powerSeriesDivisorRestriction k v).weightedOrder w = (b : ℕ∞))
    (hd : (powerSeriesDivisorRestriction k (powerSeriesJacobian ψ).det).weightedOrder w = (d : ℕ∞))
    (hfixed : ∀ j, (μ : ℕ∞) ≤ ((n * h * b : ℕ) : ℕ∞) +
      (powerSeriesDivisorRestriction k (f j)).weightedOrder w) :
    μ < h * (1 + d + (n - 1) * b) := by
  have hw : w ≠ 0 := by
    intro hz
    simp only [hz, Pi.zero_apply, Finset.sum_const_zero] at hwsum
    omega
  obtain ⟨j, hj⟩ := projectiveThreshold_divisor_strict_weighted_bound ψ k v hnormal hJ
    p f g h hthreshold hres w hw
  rw [hb, hd, hwsum, Nat.cast_one] at hj
  have hn : n = (n - 1) + 1 := by have := k.isLt; omega
  have hsplit : n * h * b = (n - 1) * h * b + h * b := by
    conv_lhs => rw [hn]
    ring
  have hlt : (μ : ℕ∞) < ((h * (1 + d + (n - 1) * b) : ℕ) : ℕ∞) := by
    calc
      _ ≤ ((n * h * b : ℕ) : ℕ∞) + (powerSeriesDivisorRestriction k (f j)).weightedOrder w := hfixed j
      _ = (((n - 1) * h * b : ℕ) : ℕ∞) +
          ((h : ℕ∞) * (b : ℕ∞) + (powerSeriesDivisorRestriction k (f j)).weightedOrder w) := by
        rw [hsplit]
        push_cast
        ring
      _ < (((n - 1) * h * b : ℕ) : ℕ∞) + (h : ℕ∞) * (1 + (d : ℕ∞)) :=
        ENat.add_lt_add_of_le_of_lt (ENat.natCast_ne_top _) le_rfl hj
      _ = _ := by push_cast; ring
  exact_mod_cast hlt

end MixedFujita
