/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TauDegreeNormalization

/-!
An explicit uniform margin for the equality-case monomial chart inequalities.
Choose a largest weight coordinate rather than minimizing over a compact
simplex. The resulting discrepancy-ratio calculation is numerical; the
geometric identification with log canonical thresholds is not proved here.
-/

@[expose] public section

namespace MixedFujita

theorem exists_coordinate_ge_average {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ) :
    ∃ i : Fin n, (∑ j, w j) / n ≤ w i := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ w
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  have hsum : (∑ j, w j) ≤ (n : ℝ) * w i := by
    calc
      (∑ j, w j) ≤ ∑ _j : Fin n, w i := Finset.sum_le_sum (fun j hj => hi j hj)
      _ = (n : ℝ) * w i := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).mpr
  simpa only [mul_comm] using hsum

theorem rationalSlice_uniform_chart_margin {n : ℕ} (hn : 0 < n) {δ : ℚ}
    (hδ : 0 ≤ δ) (w : Fin n → ℝ) (k : Fin n) (hk : w k = 0) :
    ∃ i : Fin n, (∑ j, w j * (rationalSliceTarget (fun _ => 1) δ k i j : ℝ)) ≤
      (1 - (δ : ℝ) / n) * (∑ j, w j) := by
  obtain ⟨i, hi⟩ := exists_coordinate_ge_average hn w
  refine ⟨i, ?_⟩
  rw [rationalSliceTarget_weight, hk]
  simp only [Rat.cast_one, mul_one, zero_sub]
  have hδR : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hmul := mul_le_mul_of_nonneg_left hi hδR
  calc
    (∑ j, w j) + (δ : ℝ) * -w i ≤ (∑ j, w j) - (δ : ℝ) * ((∑ j, w j) / n) := by linarith
    _ = (1 - (δ : ℝ) / n) * (∑ j, w j) := by ring

theorem rationalSlice_strict_uniform_chart_margin {n : ℕ} (hn : 0 < n) {δ : ℚ}
    (hδ : 0 < δ) (w : Fin n → ℝ) (k : Fin n)
    (hw : ∀ i, 0 ≤ w i) (hk : w k = 0) (hne : w ≠ 0) :
    ∃ i : Fin n,
      (∑ j, w j * (rationalSliceTarget (fun _ => 1) δ k i j : ℝ)) ≤
        (1 - (δ : ℝ) / n) * (∑ j, w j) ∧
      (1 - (δ : ℝ) / n) * (∑ j, w j) < ∑ j, w j := by
  obtain ⟨i, hi⟩ := rationalSlice_uniform_chart_margin hn hδ.le w k hk
  refine ⟨i, hi, ?_⟩
  have hsum : 0 < ∑ j, w j := by
    apply Finset.sum_pos'
    · exact fun j _ => hw j
    · have hex : ∃ j, w j ≠ 0 := by
        by_contra h
        apply hne
        funext j
        exact not_ne_iff.mp (not_exists.mp h j)
      obtain ⟨j, hj⟩ := hex
      exact ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hw j) (Ne.symm hj)⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hratio : 0 < (δ : ℝ) / n := div_pos hδR hnR
  nlinarith

theorem normalized_exponent_chart_margin {n : ℕ} (hn : 0 < n)
    (β : Fin n × Fin n → Fin n →₀ ℕ) {h : ℕ} (hh : 0 < h) {δ : ℚ} (hδ : 0 ≤ δ)
    (hβ : ∀ k i j, (β (k, i) j : ℚ) / h = rationalSliceTarget (fun _ => 1) δ k i j)
    (w : Fin n → ℝ) (k : Fin n) (hk : w k = 0) :
    ∃ i : Fin n, (∑ j, w j * (β (k, i) j : ℝ)) ≤
      (h : ℝ) * (1 - (δ : ℝ) / n) * (∑ j, w j) := by
  obtain ⟨i, hi⟩ := rationalSlice_uniform_chart_margin hn hδ w k hk
  have hcast (j : Fin n) : (β (k, i) j : ℝ) / h =
      (rationalSliceTarget (fun _ => 1) δ k i j : ℝ) := by
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (hβ k i j)
    simpa only [Rat.cast_div, Rat.cast_natCast] using hc
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  simp_rw [← hcast, ← mul_div_assoc] at hi
  rw [← Finset.sum_div] at hi
  refine ⟨i, ?_⟩
  have hbound := (div_le_iff₀ hhR).mp hi
  nlinarith

theorem chart_discrepancy_ratio_gap {h c S v : ℝ}
    (hh : 0 < h) (hc : 0 < c) (hc1 : c < 1) (hv : 0 < v)
    (hbound : v ≤ h * c * S) :
    1 / h < 1 / (h * c) ∧ 1 / (h * c) ≤ S / v := by
  have hprod : 0 < h * c := mul_pos hh hc
  constructor
  · apply (div_lt_div_iff₀ hh hprod).mpr
    nlinarith
  · apply (div_le_div_iff₀ hprod hv).mpr
    nlinarith

theorem equality_scaled_exponent_chart_margin {n : ℕ} (hn : 0 < n)
    (β : Fin n × Fin n → Fin n →₀ ℕ) {r j D a b : ℕ} {δ : ℚ}
    (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b) (hδ : 0 ≤ δ)
    (hβ : ∀ k i q, (β (k, i) q : ℚ) / ((D : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k i q)
    (w : Fin n → ℝ) (k : Fin n) (hk : w k = 0) :
    ∃ i : Fin n, (∑ q, w q * (((r * a) • β (k, i)) q : ℝ)) ≤
      (equalityHeight r j D b : ℝ) *
        (1 - (((a : ℚ) / b * δ : ℚ) : ℝ) / n) * (∑ q, w q) := by
  have hscaled : ∀ k i q,
      (((r * a) • β (k, i)) q : ℚ) / equalityHeight r j D b =
        rationalSliceTarget (fun _ => 1) ((a : ℚ) / b * δ) k i q := by
    intro k i q
    rw [equality_scaled_slice_coordinate (β (k, i)) k i q hr hj hD ha hb (hβ k i q)]
    unfold rationalSliceTarget
    ring
  have haQ : (0 : ℚ) ≤ a := by positivity
  have hbQ : (0 : ℚ) ≤ b := by positivity
  exact normalized_exponent_chart_margin hn (fun l => (r * a) • β l)
    (equalityHeight_pos hr hj hD hb) (mul_nonneg (div_nonneg haQ hbQ) hδ)
    hscaled w k hk

end MixedFujita
