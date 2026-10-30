/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InteriorStartBound

/-!
The lattice-average and interior estimates from an eventual lower bound on cardinalities.
No Hilbert limit is required: c j^n <= N_j already gives the strict average-degree threshold.
-/

@[expose] public section

open Filter Topology

namespace MixedFujita

/-- A cardinality lower bound suffices for the average-degree estimate (32). -/
theorem eventually_average_degree_ge_of_card_lower (n : ℕ) (hn : 0 < n)
    (E : ℕ → Finset (Fin n → ℕ)) {c : ℝ} (hc : 0 < c)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤ ((E j).card : ℝ))
    {σ : ℝ} (hσ : σ < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹) :
    ∀ᶠ j : ℕ in atTop, (E j).Nonempty ∧
      σ ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card := by
  let L : ℝ := (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹
  have hlow : Tendsto (fun j : ℕ => L - n / (j : ℝ)) atTop (𝓝 L) := by
    simpa only [sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (n : ℝ))
  filter_upwards [hN, hlow.eventually_const_lt hσ, eventually_ge_atTop 1] with j hNj hj hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hcard : (0 : ℝ) < (E j).card := (mul_pos hc (pow_pos hj0 n)).trans_le hNj
  have hne : (E j).Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  have hnorm : c ≤ ((E j).card : ℝ) / (j : ℝ) ^ n :=
    (le_div_iff₀ (pow_pos hj0 n)).mpr hNj
  have hroot := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ n.factorial * c)
    (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n.factorial))
    (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
  have hscale : ((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ =
      ((n.factorial : ℝ) * (E j).card) ^ (n : ℝ)⁻¹ / j := by
    rw [mul_div_assoc', Real.div_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hj0.le hn.ne']
  rw [hscale] at hroot
  have havg := div_le_div_of_nonneg_right (average_degree_lower_bound n hn (E j) hne) hj0.le
  have hdiv : (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card =
      ((∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ)) / (E j).card) / j := by
    rw [← Finset.sum_div]
    ring
  refine ⟨hne, ?_⟩
  rw [hdiv]
  calc σ ≤ L - n / (j : ℝ) := hj.le
    _ ≤ ((n : ℝ) / (n + 1) * ((n.factorial : ℝ) * (E j).card) ^ (n : ℝ)⁻¹ - n) / j := by
      dsimp [L]
      rw [sub_div, mul_div_assoc]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hroot (by positivity)) _
    _ ≤ _ := havg

/-- The interior inequality (7) needs a strict dimension lower bound and a uniform order bound,
without an asymptotic equality for the dimensions. -/
theorem interior_start_of_dimension_lower (n : ℕ) (hn : 0 < n)
    (E : ℕ → Finset (Fin n → ℕ)) {c b C : ℝ} (hc : 0 < c) (hb : 0 < b) (hC : 0 ≤ C)
    (hN : ∀ᶠ j : ℕ in atTop, c * (j : ℝ) ^ n ≤ ((E j).card : ℝ))
    (hord : ∀ᶠ j : ℕ in atTop, ∀ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) ≤ C * j)
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop,
      ∀ t, t₀ ≤ t → t ≤ b →
        (∑ γ ∈ E j, Real.exp (ζ * n / t - ζ * (((∑ i, γ i : ℕ) : ℝ) / j))) /
          (E j).card ≤ 1 - δ := by
  let L : ℝ := (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹
  have hσ1 : (n : ℝ) / b < ((n : ℝ) / b + L) / 2 := by dsimp [L]; linarith
  have hσ2 : ((n : ℝ) / b + L) / 2 < L := by linarith
  have hev := eventually_average_degree_ge_of_card_lower n hn E hc hN hσ2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine uniform_interior_start E (fun j γ => ((∑ i, γ i : ℕ) : ℝ) / j) hn0 hb hC hσ1
    (hev.mono fun j h => h.1) ?_ (hev.mono fun j h => h.2)
  filter_upwards [hord, eventually_ge_atTop 1] with j hj hj1 γ hγ
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  refine ⟨div_nonneg (Nat.cast_nonneg _) hj0.le, ?_⟩
  rw [div_le_iff₀ hj0]
  exact hj γ hγ

end MixedFujita
