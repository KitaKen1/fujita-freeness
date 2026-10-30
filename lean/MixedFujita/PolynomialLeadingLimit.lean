/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Tactic.Ring

/-! 普通の多項式最高次係数と自然数上の正規化極限。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open Filter Topology Polynomial Finset
namespace MixedFujita

/-- Ordinary polynomial coefficients are the limits of geometrically scaled
values, including the zero-leading-coefficient case. -/
theorem realPolynomial_tendsto_eval_div_pow_nat
    (P : ℝ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    Filter.Tendsto (fun m : ℕ => P.eval (m : ℝ) / (m : ℝ) ^ n)
      Filter.atTop (nhds (P.coeff n)) := by
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      Filter.Tendsto (fun m : ℕ => P.coeff k * ((m : ℝ) ^ k / (m : ℝ) ^ n))
        Filter.atTop (nhds (if k = n then P.coeff n else 0)) := by
    by_cases hkn : k = n
    · subst k
      simp only [ite_true]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop 1] with m hm
      have hne : (m : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (show m ≠ 0 by omega))
      rw [div_self hne, mul_one]
    · have hlt : k < n := by have := mem_range.mp hk; omega
      have h := (tendsto_pow_div_pow_atTop_zero hlt :
        Filter.Tendsto (fun x : ℝ => x ^ k / x ^ n) Filter.atTop (nhds 0)).comp
          tendsto_natCast_atTop_atTop
      simpa only [Function.comp_apply, hkn, ite_false, mul_zero] using h.const_mul (P.coeff k)
  have hs := tendsto_finsetSum (range (n + 1)) hterm
  have hsum : (∑ k ∈ range (n + 1), if k = n then P.coeff n else 0) = P.coeff n := by simp
  rw [hsum] at hs
  apply hs.congr'
  filter_upwards with m
  rw [P.eval_eq_sum_range' (n := n + 1) (by omega), Finset.sum_div]
  apply sum_congr rfl
  intro k hk
  ring


/-- The same leading-coefficient limit for an actual rational polynomial,
under the standard embedding into the reals. -/
theorem rationalPolynomial_tendsto_eval_div_pow_nat
    (P : ℚ[X]) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    Filter.Tendsto (fun m : ℕ => ((P.eval (m : ℚ) : ℚ) : ℝ) / (m : ℝ) ^ n)
      Filter.atTop (nhds (P.coeff n : ℝ)) := by
  have h := realPolynomial_tendsto_eval_div_pow_nat (P.map (Rat.castHom ℝ)) n
    (Polynomial.natDegree_map_le.trans hdeg)
  simpa only [Polynomial.coeff_map, Polynomial.eval_map, Polynomial.eval₂_at_natCast, Rat.coe_castHom] using h

end MixedFujita
