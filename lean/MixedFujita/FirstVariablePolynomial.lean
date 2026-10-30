/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.MvPolynomial.Degrees

/-! 一変数多項式の多変数埋め込みと総次数・係数分離。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Insert an ordinary rational polynomial in the first variable. -/
noncomputable def firstVariablePolynomial (r : ℕ) (P : Polynomial ℚ) :
    MvPolynomial (Fin (r + 1)) ℚ :=
  P.eval₂ MvPolynomial.C (MvPolynomial.X 0)


/-- Evaluation of the first-variable embedding is ordinary evaluation. -/
theorem firstVariablePolynomial_eval (r : ℕ) (P : Polynomial ℚ)
    (x : Fin (r + 1) → ℚ) :
    MvPolynomial.eval x (firstVariablePolynomial r P) = P.eval (x 0) := by
  rw [firstVariablePolynomial, Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ := by
    ext a
    simp
  rw [hc, MvPolynomial.eval_X, Polynomial.eval₂_id]


/-- The first-variable embedding has its ordinary total degree bound. -/
theorem firstVariablePolynomial_totalDegree_le (r : ℕ) (P : Polynomial ℚ) :
    (firstVariablePolynomial r P).totalDegree ≤ P.natDegree := by
  have hsum : firstVariablePolynomial r P =
      ∑ k ∈ range (P.natDegree + 1), MvPolynomial.C (P.coeff k) * MvPolynomial.X 0 ^ k := by
    rw [firstVariablePolynomial, Polynomial.eval₂_eq_sum_range]
  rw [hsum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  have h := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (P.coeff k) : MvPolynomial (Fin (r + 1)) ℚ) (MvPolynomial.X 0 ^ k)
  simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, zero_add] at h
  exact h.trans (by have := mem_range.mp hk; omega)


/-- Splitting the first variable sends its embedding to coefficient mapping. -/
theorem firstVariablePolynomial_finSuccEquiv (r : ℕ) (P : Polynomial ℚ) :
    MvPolynomial.finSuccEquiv ℚ r (firstVariablePolynomial r P) =
      P.map (MvPolynomial.C : ℚ →+* MvPolynomial (Fin r) ℚ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [firstVariablePolynomial, Polynomial.eval₂_add, map_add] at *
    rw [hP, hQ, Polynomial.map_add]
  | monomial k a =>
    simp only [firstVariablePolynomial, Polynomial.eval₂_monomial, map_mul, map_pow,
      MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_monomial]
    rw [MvPolynomial.finSuccEquiv_apply]
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    exact Polynomial.C_mul_X_pow_eq_monomial


/-- Splitting the first variable sends a renamed tail to a constant polynomial. -/
theorem finSuccEquiv_rename_succ (r : ℕ) (Q : MvPolynomial (Fin r) ℚ) :
    MvPolynomial.finSuccEquiv ℚ r (MvPolynomial.rename Fin.succ Q) = Polynomial.C Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ, hP, map_mul]


/-- Coefficients separate between the first variable and the renamed tail. -/
theorem firstVariablePolynomial_mul_rename_coeff
    (r : ℕ) (P : Polynomial ℚ) (Q : MvPolynomial (Fin r) ℚ)
    (m : Fin r →₀ ℕ) (i : ℕ) :
    (firstVariablePolynomial r P * MvPolynomial.rename Fin.succ Q).coeff (m.cons i) =
      P.coeff i * Q.coeff m := by
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff, map_mul, firstVariablePolynomial_finSuccEquiv,
    finSuccEquiv_rename_succ, Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.coeff_C_mul]

end MixedFujita
