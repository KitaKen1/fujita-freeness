/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! 下降階乗による実有理Newton多項式と通常の階乗規格化。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open Polynomial Finset
namespace MixedFujita

/-- The actual rational binomial polynomial, with its ordinary factorial
normalization rather than a new notion of geometric degree. -/
noncomputable def rationalBinomialPolynomial (k : ℕ) : ℚ[X] :=
  C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k


/-- The binomial polynomial evaluates to the original natural binomial coefficient. -/
theorem rationalBinomialPolynomial_eval_nat (k m : ℕ) :
    (rationalBinomialPolynomial k).eval (m : ℚ) = (m.choose k : ℚ) := by
  rw [rationalBinomialPolynomial, eval_mul, eval_C, Nat.cast_choose_eq_descPochhammer_div]
  rw [div_eq_mul_inv, mul_comm]


/-- The binomial polynomial has ordinary degree at most its index. -/
theorem rationalBinomialPolynomial_natDegree_le (k : ℕ) :
    (rationalBinomialPolynomial k).natDegree ≤ k := by
  exact (natDegree_C_mul_le _ _).trans_eq (descPochhammer_natDegree ℚ k)


/-- The top coefficient is the reciprocal factorial. -/
theorem rationalBinomialPolynomial_coeff_self (k : ℕ) :
    (rationalBinomialPolynomial k).coeff k = (k.factorial : ℚ)⁻¹ := by
  rw [rationalBinomialPolynomial, coeff_C_mul]
  have h := (monic_descPochhammer ℚ k).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  rw [h, mul_one]


/-- A finite Gregory--Newton polynomial with specified actual difference coefficients. -/
noncomputable def rationalNewtonPolynomial (n : ℕ) (c : ℕ → ℚ) : ℚ[X] :=
  ∑ k ∈ range (n + 1), C (c k) * rationalBinomialPolynomial k


/-- The finite Newton polynomial has ordinary degree at most the truncation index. -/
theorem rationalNewtonPolynomial_natDegree_le (n : ℕ) (c : ℕ → ℚ) :
    (rationalNewtonPolynomial n c).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  simp only [rationalNewtonPolynomial, finsetSum_coeff]
  apply sum_eq_zero
  intro k hk
  apply coeff_eq_zero_of_natDegree_lt
  exact (natDegree_C_mul_le _ _).trans_lt
    ((rationalBinomialPolynomial_natDegree_le k).trans_lt (lt_of_le_of_lt (by have hk' := mem_range.mp hk; omega) hN))


/-- The ordinary top coefficient of the Newton polynomial is c_n/n!. -/
theorem rationalNewtonPolynomial_coeff_top (n : ℕ) (c : ℕ → ℚ) :
    (rationalNewtonPolynomial n c).coeff n = c n / n.factorial := by
  simp only [rationalNewtonPolynomial, finsetSum_coeff, coeff_C_mul]
  rw [sum_eq_single n]
  · rw [rationalBinomialPolynomial_coeff_self, div_eq_mul_inv]
  · intro k hk hkn
    rw [coeff_eq_zero_of_natDegree_lt
      ((rationalBinomialPolynomial_natDegree_le k).trans_lt (by have := mem_range.mp hk; omega)), mul_zero]
  · intro hn
    exact False.elim (hn (mem_range.mpr (Nat.lt_succ_self n)))


/-- Factorial normalization of the ordinary top Newton coefficient. -/
theorem factorial_mul_rationalNewtonPolynomial_coeff_top (n : ℕ) (c : ℕ → ℚ) :
    (n.factorial : ℚ) * (rationalNewtonPolynomial n c).coeff n = c n := by
  rw [rationalNewtonPolynomial_coeff_top]
  have hfac : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

end MixedFujita
