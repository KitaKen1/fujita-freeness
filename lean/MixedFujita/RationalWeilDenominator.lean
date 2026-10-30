/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

/-! A finitely supported rational Weil divisor has an actual integral
numerator at one positive denominator. Coefficients in [0,1) give the exact
integral window [0,m). No Cartierness is inferred from this arithmetic. -/

@[expose] public section

namespace MixedFujita

/-- Clear all denominators of an actual finitely supported rational divisor. -/
theorem rational_finsupp_exists_integral_multiple {ι : Type*} (b : ι →₀ ℚ) :
    ∃ (m : ℕ), 0 < m ∧ ∃ E : ι →₀ ℤ, ∀ i, (E i : ℚ) = (m : ℚ) * b i := by
  classical
  induction b using Finsupp.induction_linear with
  | zero => exact ⟨1, by omega, 0, by simp⟩
  | add b c hb hc =>
    obtain ⟨m, hm, E, hE⟩ := hb
    obtain ⟨n, hn, F, hF⟩ := hc
    refine ⟨m * n, Nat.mul_pos hm hn, n • E + m • F, fun i => ?_⟩
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Int.cast_add,
      Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [hE i, hF i]
    ring
  | single a q =>
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hq : (q.num : ℚ) = (q.den : ℚ) * q := by
      calc
        (q.num : ℚ) = (q.den : ℚ) * ((q.num : ℚ) / q.den) := by field_simp [hden]
        _ = (q.den : ℚ) * q := by rw [q.num_div_den]
    refine ⟨q.den, q.pos, Finsupp.single a q.num, fun i => ?_⟩
    by_cases hi : i = a
    · subst i
      simpa only [Finsupp.single_eq_same] using hq
    · simp [Finsupp.single_apply, hi, Ne.symm hi]

/-- Rational boundary coefficients give an actual nonnegative integral numerator strictly below its denominator. -/
theorem rational_finsupp_exists_integral_multiple_coefficients_mem_Ico
    {ι : Type*} (b : ι →₀ ℚ) (hb : ∀ i, b i ∈ Set.Ico (0 : ℚ) 1) :
    ∃ (m : ℕ), 0 < m ∧ ∃ E : ι →₀ ℤ,
      (∀ i, (E i : ℚ) = (m : ℚ) * b i) ∧ ∀ i, 0 ≤ E i ∧ E i < (m : ℤ) := by
  obtain ⟨m, hm, E, hE⟩ := rational_finsupp_exists_integral_multiple b
  refine ⟨m, hm, E, hE, fun i => ?_⟩
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hnonneg : (0 : ℚ) ≤ (E i : ℚ) := by rw [hE i]; exact mul_nonneg hmQ.le (hb i).1
  have hlt : (E i : ℚ) < (m : ℚ) := by
    rw [hE i]
    exact (mul_lt_mul_of_pos_left (hb i).2 hmQ).trans_eq (mul_one _)
  constructor
  · exact_mod_cast hnonneg
  · exact_mod_cast hlt

end MixedFujita
