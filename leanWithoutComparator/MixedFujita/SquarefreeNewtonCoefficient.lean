/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MultivariateNewtonPolynomial
public import Mathlib.Tactic.Ring

/-! 平方因子を持たない最高次係数と整数混合差分の一致。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The ordinary squarefree exponent containing every variable exactly once. -/
noncomputable def squarefreeExponent : (r : ℕ) → Fin r →₀ ℕ
  | 0 => 0
  | r + 1 => (squarefreeExponent r).cons 1


/-- Every variable in the squarefree exponent has exponent one. -/
theorem squarefreeExponent_apply (r : ℕ) (i : Fin r) : squarefreeExponent r i = 1 := by
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j


/-- The squarefree monomial has ordinary total degree equal to the number of variables. -/
theorem squarefreeExponent_weight (r : ℕ) :
    (∑ i ∈ (squarefreeExponent r).support, squarefreeExponent r i) = r := by
  have hs : (squarefreeExponent r).support = univ := by
    ext i
    simp [Finsupp.mem_support_iff, squarefreeExponent_apply]
  rw [hs]
  simp only [squarefreeExponent_apply, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]


/-- The squarefree top coefficient is EXACTLY the original iterated mixed
difference, with no factorial and no extra polynomiality premise. -/
theorem multivariateNewtonPolynomial_squarefree_top_coeff
    {A : Type*} [AddCommGroup A] (r : ℕ) (D : Fin r → A) (f : A → ℤ) (E : A) :
    (multivariateNewtonPolynomial r r D f E).coeff (squarefreeExponent r) =
      (mixedForwardDifference (List.ofFn D) f E : ℚ) := by
  induction r generalizing f E with
  | zero =>
    change (MvPolynomial.C (f E : ℚ) : MvPolynomial (Fin 0) ℚ).coeff 0 = (f E : ℚ)
    simp only [MvPolynomial.coeff_C, ite_true]
  | succ r ih =>
    change (MvPolynomial.coeffAddMonoidHom ((squarefreeExponent r).cons 1))
      (∑ k ∈ range (r + 1 + 1), firstVariablePolynomial r (rationalBinomialPolynomial k) *
        MvPolynomial.rename Fin.succ (multivariateNewtonPolynomial r (r + 1 - k)
          (fun i => D i.succ) (mixedForwardDifference (List.replicate k (D 0)) f) E)) = _
    rw [map_sum]
    simp only [MvPolynomial.coeffAddMonoidHom_apply, firstVariablePolynomial_mul_rename_coeff]
    rw [sum_eq_single 1]
    · have hb : (rationalBinomialPolynomial 1).coeff 1 = 1 := by
        rw [rationalBinomialPolynomial_coeff_self]
        norm_num
      rw [hb, one_mul, Nat.add_sub_cancel_right]
      rw [ih]
      change (mixedForwardDifference (List.ofFn (fun i => D i.succ)) (fwdDiff (D 0) f) E : ℚ) = _
      rw [mixedForwardDifference_right_singleton, List.ofFn_succ]
    · intro k hk hkn
      by_cases hk0 : k = 0
      · subst k
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          ((rationalBinomialPolynomial_natDegree_le 0).trans_lt (by omega)), zero_mul]
      · have hk2 : 2 ≤ k := by omega
        have hkr : k ≤ r + 1 := by have := mem_range.mp hk; omega
        have hd : (multivariateNewtonPolynomial r (r + 1 - k) (fun i => D i.succ)
            (mixedForwardDifference (List.replicate k (D 0)) f) E).totalDegree < r :=
          (multivariateNewtonPolynomial_totalDegree_le ..).trans_lt (by omega)
        rw [MvPolynomial.coeff_eq_zero_of_totalDegree_lt
          (by rw [squarefreeExponent_weight]; exact hd), mul_zero]
    · intro hnot
      exact False.elim (hnot (mem_range.mpr (by omega)))

end MixedFujita
