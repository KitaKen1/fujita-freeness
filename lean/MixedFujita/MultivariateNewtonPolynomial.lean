/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.FirstVariablePolynomial
public import MixedFujita.MixedForwardDifferenceComposition
public import MixedFujita.IntegerNewtonReconstruction

/-! 総次数を切り詰める再帰的多変数Newton展開と全整数評価。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A total-degree-truncated multivariate Newton polynomial, recursively
splitting variables and decreasing the residual degree budget. -/
noncomputable def multivariateNewtonPolynomial {A : Type*} [AddCommGroup A] :
    (r : ℕ) → ℕ → (Fin r → A) → (A → ℤ) → A → MvPolynomial (Fin r) ℚ
  | 0, _, _, f, E => MvPolynomial.C (f E : ℚ)
  | r + 1, n, D, f, E => ∑ k ∈ range (n + 1),
      firstVariablePolynomial r (rationalBinomialPolynomial k) *
        MvPolynomial.rename Fin.succ (multivariateNewtonPolynomial r (n - k)
          (fun i => D i.succ) (mixedForwardDifference (List.replicate k (D 0)) f) E)


/-- The constructed multivariate polynomial has actual TOTAL degree at most
the geometric budget, rather than only a bound in each individual variable. -/
theorem multivariateNewtonPolynomial_totalDegree_le {A : Type*} [AddCommGroup A]
    (r n : ℕ) (D : Fin r → A) (f : A → ℤ) (E : A) :
    (multivariateNewtonPolynomial r n D f E).totalDegree ≤ n := by
  induction r generalizing n f E with
  | zero => simp only [multivariateNewtonPolynomial, MvPolynomial.totalDegree_C, Nat.zero_le]
  | succ r ih =>
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k hk
    have hk' : k ≤ n := by have := mem_range.mp hk; omega
    have h₁ := (firstVariablePolynomial_totalDegree_le r (rationalBinomialPolynomial k)).trans
      (rationalBinomialPolynomial_natDegree_le k)
    have h₂ := (MvPolynomial.totalDegree_rename_le Fin.succ
      (multivariateNewtonPolynomial r (n - k) (fun i => D i.succ)
        (mixedForwardDifference (List.replicate k (D 0)) f) E )).trans (ih _ _ _ _)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)


/-- Under actual global mixed nilpotence, this multivariate polynomial
agrees with the original integer function on EVERY signed integer tuple. -/
theorem multivariateNewtonPolynomial_eval_int_of_mixed_nilpotence
    {A : Type*} [AddCommGroup A] (r n : ℕ) (D : Fin r → A) (f : A → ℤ) (E : A)
    (hzero : ∀ L : List A, n < L.length → ∀ F : A, mixedForwardDifference L f F = 0)
    (z : Fin r → ℤ) :
    MvPolynomial.eval (fun i => (z i : ℚ)) (multivariateNewtonPolynomial r n D f E) =
      (f (E + ∑ i, z i • D i) : ℚ) := by
  induction r generalizing n f E with
  | zero => simp [multivariateNewtonPolynomial]
  | succ r ih =>
    let V : A := ∑ i : Fin r, z i.succ • D i.succ
    have h₀ : ∀ t : ℤ, mixedForwardDifference (List.replicate (n + 1) (D 0)) f
        ((E + V) + t • D 0) = 0 := by
      intro t
      exact hzero _ (by simp only [List.length_replicate]; omega) _
    have h := rationalNewtonPolynomial_eval_affine_of_mixed_nilpotence f n (D 0) (E + V) h₀ (z 0)
    have harg : E + ∑ i, z i • D i = (E + V) + z 0 • D 0 := by
      rw [Fin.sum_univ_succ]
      dsimp [V]
      abel
    rw [harg, ← h]
    simp only [multivariateNewtonPolynomial, map_sum, map_mul, firstVariablePolynomial_eval,
      MvPolynomial.eval_rename, rationalNewtonPolynomial, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by have := mem_range.mp hk; omega
    have htail : ∀ L : List A, n - k < L.length → ∀ F : A,
        mixedForwardDifference L (mixedForwardDifference (List.replicate k (D 0)) f) F = 0 := by
      intro L hL F
      rw [← mixedForwardDifference_append]
      exact hzero _ (by simp only [List.length_append, List.length_replicate]; omega) _
    have ht := ih (n - k) (fun i => D i.succ)
      (mixedForwardDifference (List.replicate k (D 0)) f) E htail (fun i => z i.succ)
    change (rationalBinomialPolynomial k).eval (z 0 : ℚ) *
      MvPolynomial.eval (fun i => (z i.succ : ℚ))
        (multivariateNewtonPolynomial r (n - k) (fun i => D i.succ)
          (mixedForwardDifference (List.replicate k (D 0)) f) E) = _
    rw [ht]
    exact mul_comm _ _

end MixedFujita
