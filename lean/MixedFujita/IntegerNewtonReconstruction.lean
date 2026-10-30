/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.RationalNewtonPolynomial
public import MixedFujita.MixedForwardDifferenceLinearity
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Algebra.Polynomial.Roots

/-! 有限差分から全整数値を復元するNewton公式・負整数と一意性。 See reports/check-222-euler-newton-hilbert-normalization.json for the verified scope. General multivariate intersection identification and mixed ample-pullback positivity remain unproved. -/

@[expose] public section
open Polynomial Finset
namespace MixedFujita

/-- Zero iterated differences remain zero in every higher order. -/
theorem fwdDiff_iter_eq_zero_of_order_ge {A : Type*} [AddCommMonoid A]
    (H : A) (f : A → ℚ) (N : ℕ) (hzero : (fwdDiff H)^[N] f = 0)
    (k : ℕ) (hk : N ≤ k) : (fwdDiff H)^[k] f = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [add_comm, Function.iterate_add_apply, hzero]
  ext x
  simp only [fwdDiff_iter_eq_sum_shift, Pi.zero_apply, smul_zero, sum_const_zero]


/-- The existing Gregory--Newton formula truncates at the proved geometric
nilpotence bound, with no assumed polynomial supplied. -/
theorem finite_newton_formula_of_iter_fwdDiff_zero
    (f : ℤ → ℚ) (n : ℕ) (hzero : (fwdDiff (1 : ℤ))^[n + 1] f = 0) (m : ℕ) :
    f (m : ℤ) = ∑ k ∈ range (n + 1), (m.choose k : ℚ) *
      ((fwdDiff (1 : ℤ))^[k] f) 0 := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℤ) f m 0
  simp only [zero_add, nsmul_eq_mul, mul_one] at h
  rw [h]
  let N := max m n
  have hm : (∑ k ∈ range (m + 1), (m.choose k : ℚ) * ((fwdDiff (1 : ℤ))^[k] f) 0) =
      ∑ k ∈ range (N + 1), (m.choose k : ℚ) * ((fwdDiff (1 : ℤ))^[k] f) 0 := by
    apply sum_subset (range_mono (Nat.succ_le_succ (le_max_left m n)))
    intro k hk hknot
    have hmk : m < k := by
      have hkm : m + 1 ≤ k := by simpa only [mem_range, not_lt] using hknot
      omega
    rw [Nat.choose_eq_zero_of_lt hmk, Nat.cast_zero, zero_mul]
  have hn : (∑ k ∈ range (n + 1), (m.choose k : ℚ) * ((fwdDiff (1 : ℤ))^[k] f) 0) =
      ∑ k ∈ range (N + 1), (m.choose k : ℚ) * ((fwdDiff (1 : ℤ))^[k] f) 0 := by
    apply sum_subset (range_mono (Nat.succ_le_succ (le_max_right m n)))
    intro k hk hknot
    have hnk : n + 1 ≤ k := by simpa only [mem_range, not_lt] using hknot
    rw [fwdDiff_iter_eq_zero_of_order_ge (1 : ℤ) f (n + 1) hzero k hnk, Pi.zero_apply, mul_zero]
  exact hm.trans hn.symm


/-- The actual finite Newton polynomial represents every nonnegative value. -/
theorem rationalNewtonPolynomial_eval_nat_of_iter_fwdDiff_zero
    (f : ℤ → ℚ) (n : ℕ) (hzero : (fwdDiff (1 : ℤ))^[n + 1] f = 0) (m : ℕ) :
    (rationalNewtonPolynomial n (fun k => ((fwdDiff (1 : ℤ))^[k] f) 0)).eval (m : ℚ) =
      f (m : ℤ) := by
  rw [finite_newton_formula_of_iter_fwdDiff_zero f n hzero m]
  simp only [rationalNewtonPolynomial, eval_finsetSum, eval_mul, eval_C,
    rationalBinomialPolynomial_eval_nat, mul_comm]


/-- Forward differences commute with the actual integer-to-rational embedding. -/
theorem fwdDiff_iter_comp_intCast (f : ℚ → ℚ) (k : ℕ) (z : ℤ) :
    ((fwdDiff (1 : ℤ))^[k] (fun t : ℤ => f (t : ℚ))) z =
      ((fwdDiff (1 : ℚ))^[k] f) (z : ℚ) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [fwdDiff, ih, Int.cast_add, Int.cast_one]


/-- Iterated forward differences preserve subtraction of rational functions. -/
theorem fwdDiff_iter_sub_functions {A : Type*} [AddCommMonoid A]
    (H : A) (f g : A → ℚ) (k : ℕ) :
    (fwdDiff H)^[k] (f - g) = (fwdDiff H)^[k] f - (fwdDiff H)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    ext x
    simp only [fwdDiff, Pi.sub_apply]
    ring


/-- A function with nilpotent forward differences is determined on all
integers by its nonnegative values, including every negative integer. -/
theorem eq_zero_of_iter_fwdDiff_zero_of_nat_eq_zero
    (N : ℕ) (f : ℤ → ℚ) (hzero : (fwdDiff (1 : ℤ))^[N] f = 0)
    (hnat : ∀ m : ℕ, f (m : ℤ) = 0) : f = 0 := by
  induction N generalizing f with
  | zero => exact hzero
  | succ N ih =>
    have hz : (fwdDiff (1 : ℤ))^[N] (fwdDiff (1 : ℤ) f) = 0 := by
      simpa only [Function.iterate_succ_apply] using hzero
    have hn (m : ℕ) : fwdDiff (1 : ℤ) f (m : ℤ) = 0 := by
      change f ((m : ℤ) + 1) - f (m : ℤ) = 0
      rw [show (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) by omega, hnat, hnat, sub_self]
    have hdiff := ih (fwdDiff (1 : ℤ) f) hz hn
    have hper : Function.Periodic f 1 := fun z => sub_eq_zero.mp (congrFun hdiff z)
    ext z
    change f z = 0
    calc f z = f 0 := by simpa only [Int.cast_id, mul_one] using hper.int_mul_eq z
         _ = 0 := hnat 0


/-- The finite Newton polynomial represents the actual function on ALL
integers. Negative powers follow from nilpotence, without an extra equality
or polynomiality premise. -/
theorem rationalNewtonPolynomial_eval_int_of_iter_fwdDiff_zero
    (f : ℤ → ℚ) (n : ℕ) (hzero : (fwdDiff (1 : ℤ))^[n + 1] f = 0) (z : ℤ) :
    (rationalNewtonPolynomial n (fun k => ((fwdDiff (1 : ℤ))^[k] f) 0)).eval (z : ℚ) = f z := by
  let P := rationalNewtonPolynomial n (fun k => ((fwdDiff (1 : ℤ))^[k] f) 0)
  let g : ℤ → ℚ := fun t => P.eval (t : ℚ)
  have hP : (fwdDiff (1 : ℚ))^[n + 1] P.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt
      ((rationalNewtonPolynomial_natDegree_le n _).trans_lt (Nat.lt_succ_self n))
  have hg : (fwdDiff (1 : ℤ))^[n + 1] g = 0 := by
    ext t
    change ((fwdDiff (1 : ℤ))^[n + 1] (fun z : ℤ => P.eval (z : ℚ))) t = 0
    exact (fwdDiff_iter_comp_intCast P.eval (n + 1) t).trans (congrFun hP (t : ℚ))
  have hsub : (fwdDiff (1 : ℤ))^[n + 1] (f - g) = 0 := by
    rw [fwdDiff_iter_sub_functions, hzero, hg, sub_self]
  have hnat (m : ℕ) : (f - g) (m : ℤ) = 0 := by
    change f (m : ℤ) - P.eval ((m : ℤ) : ℚ) = 0
    rw [Int.cast_natCast, rationalNewtonPolynomial_eval_nat_of_iter_fwdDiff_zero f n hzero m, sub_self]
  have hz := congrFun (eq_zero_of_iter_fwdDiff_zero_of_nat_eq_zero (n + 1) (f - g) hsub hnat) z
  exact (sub_eq_zero.mp hz).symm


/-- Forward differences along integer multiples of an actual direction
are exactly the original mixed differences, including the scalar embedding. -/
theorem fwdDiff_iter_intCast_affine {A : Type*} [AddCommGroup A]
    (f : A → ℤ) (H E : A) (k : ℕ) (z : ℤ) :
    ((fwdDiff (1 : ℤ))^[k] (fun t : ℤ => (f (E + t • H) : ℚ))) z =
      (mixedForwardDifference (List.replicate k H) f (E + z • H) : ℚ) := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((fwdDiff (1 : ℤ))^[k] (fun t : ℤ => (f (E + t • H) : ℚ))) (z + 1) -
      ((fwdDiff (1 : ℤ))^[k] (fun t : ℤ => (f (E + t • H) : ℚ))) z = _
    rw [ih, ih, List.replicate_succ, mixedForwardDifference_cons, Int.cast_sub]
    congr 1
    simp only [add_zsmul, one_zsmul, add_assoc]


/-- Pure arithmetic transfer from the proved mixed-difference nilpotence to
one actual rational polynomial on all integer multiples of the direction. -/
theorem rationalNewtonPolynomial_eval_affine_of_mixed_nilpotence
    {A : Type*} [AddCommGroup A] (f : A → ℤ) (n : ℕ) (H E : A)
    (hzero : ∀ z : ℤ, mixedForwardDifference (List.replicate (n + 1) H) f (E + z • H) = 0)
    (z : ℤ) :
    (rationalNewtonPolynomial n (fun k =>
      (mixedForwardDifference (List.replicate k H) f E : ℚ))).eval (z : ℚ) =
        (f (E + z • H) : ℚ) := by
  let g : ℤ → ℚ := fun t => (f (E + t • H) : ℚ)
  have hg : (fwdDiff (1 : ℤ))^[n + 1] g = 0 := by
    ext t
    exact (fwdDiff_iter_intCast_affine f H E (n + 1) t).trans (by rw [hzero]; rfl)
  have hc : (fun k => ((fwdDiff (1 : ℤ))^[k] g) 0) =
      fun k => (mixedForwardDifference (List.replicate k H) f E : ℚ) := by
    funext k
    have h := fwdDiff_iter_intCast_affine f H E k 0
    simpa only [zero_zsmul, add_zero] using h
  have h := rationalNewtonPolynomial_eval_int_of_iter_fwdDiff_zero g n hg z
  rw [hc] at h
  exact h


/-- A rational polynomial is determined by its natural-number values. -/
theorem rationalPolynomial_eq_of_eval_nat (P Q : ℚ[X])
    (h : ∀ m : ℕ, P.eval (m : ℚ) = Q.eval (m : ℚ)) : P = Q := by
  apply P.eq_of_infinite_eval_eq Q
  apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective
    (fun m : ℕ => (m : ℚ)))).mono
  rintro x ⟨m, rfl⟩
  exact h m

end MixedFujita
