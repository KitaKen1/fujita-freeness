/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
From the multiples of k to all degrees. Let h(j) = h^0(jA). Multiplying by a nonzero section of
eA is injective, so h(j) ≤ h(j + e) whenever eA has a nonzero section; suppose this holds for all
e ≥ e₀. If h(kq)/(kq)^d → c, then h(j)/j^d → c for all j: write j between k q₁ = j - e and
k q₂ = j + e' with e, e' ≥ e₀ and e, e' < e₀ + k, so h(k q₁) ≤ h(j) ≤ h(k q₂) and
k q₁ / j, k q₂ / j → 1. This is the passage of Lemma 4 to all degrees ("各剰余類に十分大きい h_r を
固定して…全次数への単射") and of the Hilbert asymptotics from a very ample multiple kA to A; the
existence of the nonzero sections is the input.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

theorem tendsto_ratio_of_bounded_shift {g : ℕ → ℕ} {C : ℕ}
    (hlow : ∀ j, j ≤ g j + C) (hup : ∀ j, g j ≤ j + C) :
    Tendsto (fun j : ℕ => (g j : ℝ) / j) atTop (𝓝 1) := by
  have hC : Tendsto (fun j : ℕ => (C : ℝ) / j) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (C : ℝ)
  have hlo : Tendsto (fun j : ℕ => 1 - (C : ℝ) / j) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hC
  have hhi : Tendsto (fun j : ℕ => 1 + (C : ℝ) / j) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hj0, one_mul]
    exact_mod_cast hlow j
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    rw [div_le_iff₀ hj0, add_mul, one_mul, div_mul_cancel₀ _ hj0.ne']
    exact_mod_cast hup j

/-- The residue sandwich: monotonicity along all shifts e ≥ e₀ carries the asymptotics along the
multiples of k to all degrees. -/
theorem tendsto_of_residue_sandwich {h : ℕ → ℝ} {k : ℕ} (hk : 0 < k) {d : ℕ} {c : ℝ} (e₀ : ℕ)
    (hmono : ∀ j e, e₀ ≤ e → h j ≤ h (j + e))
    (hlim : Tendsto (fun q : ℕ => h (k * q) / ((k * q : ℕ) : ℝ) ^ d) atTop (𝓝 c)) :
    Tendsto (fun j : ℕ => h j / (j : ℝ) ^ d) atTop (𝓝 c) := by
  -- lower and upper multiples of k
  set q₁ : ℕ → ℕ := fun j => (j - e₀) / k with hq₁
  set q₂ : ℕ → ℕ := fun j => (j + e₀) / k + 1 with hq₂
  have hA : ∀ j, k * q₁ j ≤ j - e₀ := by
    intro j
    simp only [hq₁]
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  have hB : ∀ j, j - e₀ < k * q₁ j + k := by
    intro j
    have h1 := Nat.lt_mul_div_succ (j - e₀) hk
    simp only [hq₁]
    rw [Nat.mul_add, mul_one] at h1
    exact h1
  have hC : ∀ j, k * q₂ j ≤ j + e₀ + k := by
    intro j
    have h1 : k * ((j + e₀) / k) ≤ j + e₀ := by
      rw [mul_comm]
      exact Nat.div_mul_le_self _ _
    simp only [hq₂]
    rw [Nat.mul_add, mul_one]
    omega
  have hD : ∀ j, j + e₀ < k * q₂ j := by
    intro j
    have h1 := Nat.lt_mul_div_succ (j + e₀) hk
    simp only [hq₂]
    exact h1
  have hq₁ge : ∀ j, j ≤ k * q₁ j + (e₀ + k) := by
    intro j
    have := hB j
    omega
  have hq₂ge : ∀ j, j + e₀ ≤ k * q₂ j := fun j => (hD j).le
  have hq₂le : ∀ j, k * q₂ j ≤ j + (e₀ + k) := by
    intro j
    have := hC j
    omega
  -- the sandwich
  have hlow : ∀ j, e₀ ≤ j → h (k * q₁ j) ≤ h j := by
    intro j hj
    have h1 := hA j
    have := hmono (k * q₁ j) (j - k * q₁ j) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  have hup : ∀ j, h j ≤ h (k * q₂ j) := by
    intro j
    have h1 := hD j
    have := hmono j (k * q₂ j - j) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  -- the ratios k q / j tend to 1
  have hr₁ : Tendsto (fun j : ℕ => ((k * q₁ j : ℕ) : ℝ) / j) atTop (𝓝 1) :=
    tendsto_ratio_of_bounded_shift (g := fun j => k * q₁ j) (C := e₀ + k) hq₁ge
      (fun j => by have := hA j; omega)
  have hr₂ : Tendsto (fun j : ℕ => ((k * q₂ j : ℕ) : ℝ) / j) atTop (𝓝 1) :=
    tendsto_ratio_of_bounded_shift (g := fun j => k * q₂ j) (C := e₀ + k)
      (fun j => by have := hq₂ge j; omega) hq₂le
  -- q₁, q₂ → ∞
  have hq₁top : Tendsto q₁ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨k * b + e₀ + k, fun j hj => ?_⟩
    have := hq₁ge j
    by_contra hlt
    push Not at hlt
    have h2 : k * q₁ j + k ≤ k * b := by
      have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hlt)
      rw [Nat.mul_succ] at this
      exact this
    omega
  have hq₂top : Tendsto q₂ atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨k * b, fun j hj => ?_⟩
    have := hq₂ge j
    by_contra hlt
    push Not at hlt
    have h2 : k * q₂ j + k ≤ k * b := by
      have := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hlt)
      rw [Nat.mul_succ] at this
      exact this
    have hk1 : 1 ≤ k := hk
    omega
  have hL₁ := (hlim.comp hq₁top).mul (hr₁.pow d)
  have hL₂ := (hlim.comp hq₂top).mul (hr₂.pow d)
  rw [one_pow, mul_one] at hL₁ hL₂
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL₁ hL₂ ?_ ?_
  · filter_upwards [eventually_ge_atTop (e₀ + k + 1)] with j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hkq : (0 : ℝ) < ((k * q₁ j : ℕ) : ℝ) := by
      have := hq₁ge j
      exact_mod_cast (show 0 < k * q₁ j by omega)
    simp only [Function.comp]
    rw [div_pow, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero d hkq.ne')]
    exact div_le_div_of_nonneg_right (hlow j (by omega)) (pow_nonneg hj0.le d)
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    have hkq : (0 : ℝ) < ((k * q₂ j : ℕ) : ℝ) := by
      have := hq₂ge j
      exact_mod_cast (show 0 < k * q₂ j by omega)
    simp only [Function.comp]
    rw [div_pow, ← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero d hkq.ne')]
    exact div_le_div_of_nonneg_right (hup j) (pow_nonneg hj0.le d)

end MixedFujita
