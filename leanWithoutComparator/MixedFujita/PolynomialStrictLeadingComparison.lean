/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialLeadingLimit
public import Mathlib.Tactic

/-! 最高次係数から十分大きい整数での厳密多項式比較。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
namespace MixedFujita
set_option maxHeartbeats 1600000

/-- Strict leading-coefficient dominance proves an eventual strict
polynomial count comparison, without an explicit numerical threshold. -/
theorem rationalPolynomial_eventually_mul_eval_lt_of_top_coeff
    (P Q : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n + 1)
    (hQ : Q.natDegree ≤ n) (hcoeff : Q.coeff n < P.coeff (n + 1)) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → (m : ℚ) * Q.eval (m : ℚ) < P.eval (m : ℚ) := by
  let R := P - Polynomial.X * Q
  have hdeg : R.natDegree ≤ n + 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    refine max_le hP ?_
    have h := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℚ)) (q := Q)
    simp only [Polynomial.natDegree_X] at h
    omega
  have hc : 0 < R.coeff (n + 1) := by
    simp only [R, Polynomial.coeff_sub, Polynomial.coeff_X_mul]
    exact sub_pos.mpr hcoeff
  have hcR : (0 : ℝ) < (R.coeff (n + 1) : ℝ) := by exact_mod_cast hc
  have h := (rationalPolynomial_tendsto_eval_div_pow_nat R (n + 1) hdeg).eventually_const_lt hcR
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨max m₀ 1, fun m hm => ?_⟩
  have hden : (0 : ℝ) < (m : ℝ) ^ (n + 1) :=
    pow_pos (by exact_mod_cast (show 0 < m by omega)) _
  have hn : (0 : ℝ) < ((R.eval (m : ℚ) : ℚ) : ℝ) :=
    (div_pos_iff_of_pos_right hden).mp (hm₀ m (by omega))
  have hnQ : (0 : ℚ) < R.eval (m : ℚ) := by exact_mod_cast hn
  simpa only [R, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, sub_pos] using hnQ

end MixedFujita
