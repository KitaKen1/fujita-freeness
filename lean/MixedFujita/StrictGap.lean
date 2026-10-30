/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
The explicit analytic gap in Section 4, after equation (integral), of the
manuscript. These are unconditional real-analysis lemmas. The geometric
derivation of the moment bound is a separate, unfinished dependency.
-/

@[expose] public section

namespace MixedFujita

open MeasureTheory

/-- The moment appearing after the two limiting operations in Section 4. -/
noncomputable def exponentialMoment (n : ℕ) (c : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s ^ n * Real.exp ((1 - s) * c)

theorem integral_linear_weight (n : ℕ) (c : ℝ) :
    (∫ s in (0 : ℝ)..1, s ^ n * (1 + (1 - s) * c)) =
      1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  have hp (k : ℕ) : IntervalIntegrable (fun s : ℝ => s ^ k) volume 0 1 :=
    (continuous_id.pow k).intervalIntegrable 0 1
  have heq : (fun s : ℝ => s ^ n * (1 + (1 - s) * c)) =
      (fun s : ℝ => s ^ n + c * (s ^ n - s ^ (n + 1))) := by
    funext s
    rw [pow_succ]
    ring
  rw [heq, intervalIntegral.integral_add (hp n) (((hp n).sub (hp (n + 1))).const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hp n) (hp (n + 1)),
    integral_pow, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add,
    Nat.cast_one]
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 1 + 1 : ℝ) ≠ 0 := by positivity
  have hn3 : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `exp u ≥ 1 + u` is sufficient; no exact exponential integral is needed. -/
theorem exponentialMoment_lower_bound (n : ℕ) (c : ℝ) :
    1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ)) ≤
      exponentialMoment n c := by
  rw [← integral_linear_weight n c]
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
  · exact ((continuous_id.pow n).mul
      (continuous_const.add ((continuous_const.sub continuous_id).mul continuous_const))).intervalIntegrable 0 1
  · exact ((continuous_id.pow n).mul
      (Real.continuous_exp.comp
        ((continuous_const.sub continuous_id).mul continuous_const))).intervalIntegrable 0 1
  · intro s hs
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.1 n)
    simpa only [add_comm] using Real.add_one_le_exp ((1 - s) * c)

/-- The paper's explicit positive margin, using `lam b = n + 1`. -/
theorem scaled_exponentialMoment_lower_bound (n : ℕ) {a b lam : ℝ}
    (hb : 0 < b) (hlam : lam * b = n + 1) :
    (1 + a / (b * (n + 2 : ℝ))) / b ≤ lam * exponentialMoment n (a / b) := by
  have hlameq : lam = (n + 1 : ℝ) / b := (eq_div_iff hb.ne').mpr hlam
  have hlampos : 0 < lam := by rw [hlameq]; positivity
  have h := mul_le_mul_of_nonneg_left (exponentialMoment_lower_bound n (a / b)) hlampos.le
  have heq : lam * (1 / (n + 1 : ℝ) + (a / b) / ((n + 1 : ℝ) * (n + 2 : ℝ))) =
      (1 + a / (b * (n + 2 : ℝ))) / b := by
    rw [hlameq]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp
  rwa [heq] at h

/-- A concrete choice of `t`, also respecting any prescribed `t₀ < b`. -/
theorem exists_parameter_with_gap {b β t₀ : ℝ}
    (hb : 0 < b) (hβ : 0 < β) (ht₀ : t₀ < b) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ 1 / t < (1 + β) / b := by
  let u := b * (2 + β) / (2 * (1 + β))
  have hden : 0 < 2 * (1 + β) := by positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hub : u < b := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hb hβ]
  have hmargin : b < (1 + β) * u := by
    have heq : u * (2 * (1 + β)) = b * (2 + β) := by
      dsimp [u]
      exact div_mul_cancel₀ _ hden.ne'
    nlinarith [mul_pos hb hβ]
  refine ⟨max t₀ u, le_max_left _ _, lt_of_lt_of_le hu (le_max_right _ _),
    max_lt ht₀ hub, ?_⟩
  have ht : 0 < max t₀ u := lt_of_lt_of_le hu (le_max_right _ _)
  apply (div_lt_div_iff₀ ht hb).mpr
  have hmul := mul_le_mul_of_nonneg_left (le_max_right t₀ u) (by positivity : 0 ≤ 1 + β)
  nlinarith

/-- End of the numerical contradiction in the point-center argument. -/
theorem exists_scaled_moment_gap (n : ℕ) {a b lam t₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlam : lam * b = n + 1) (ht₀ : t₀ < b) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧
      1 / t < lam * exponentialMoment n (a / b) := by
  have hβ : 0 < a / (b * (n + 2 : ℝ)) := by positivity
  obtain ⟨t, ht₀', ht, htb, hgap⟩ := exists_parameter_with_gap hb hβ ht₀
  exact ⟨t, ht₀', ht, htb,
    hgap.trans_le (scaled_exponentialMoment_lower_bound n hb hlam)⟩

end MixedFujita
