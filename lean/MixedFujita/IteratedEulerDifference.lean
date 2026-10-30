/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.Ring

/-!
The algebra of iterated Cartier-cut Euler differences. The recurrence
c(r+1,j) = c(r,j) - c(r,j+1) has an explicit binomial solution, derived from
Mathlib's forward-difference theorem. The values here are integers, not
postulated geometric Euler characteristics. Constructing actual Cartier-cut
flags and proving their cohomology comparison and finiteness remain separate.
-/

@[expose] public section
namespace MixedFujita
open Finset Function

def integerEulerCutDifference (F : ℕ → ℤ) (r j : ℕ) : ℤ :=
  (-1 : ℤ) ^ r * ((fwdDiff (1 : ℕ))^[r] F) j

theorem integerEulerCutDifference_zero (F : ℕ → ℤ) (j : ℕ) :
    integerEulerCutDifference F 0 j = F j := by
  simp [integerEulerCutDifference]

theorem integerEulerCutDifference_succ (F : ℕ → ℤ) (r j : ℕ) :
    integerEulerCutDifference F (r + 1) j =
      integerEulerCutDifference F r j - integerEulerCutDifference F r (j + 1) := by
  simp only [integerEulerCutDifference, Function.iterate_succ_apply', fwdDiff, pow_succ]
  ring

theorem integerEulerCutSign_cancel (r k : ℕ) (hk : k ≤ r) :
    (-1 : ℤ) ^ r * (-1 : ℤ) ^ (r - k) = (-1 : ℤ) ^ k := by
  have hp : (-1 : ℤ) ^ r = (-1 : ℤ) ^ k * (-1 : ℤ) ^ (r - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hp, mul_assoc, ← sq, ← pow_mul, Nat.mul_comm (r - k) 2, pow_mul,
    neg_one_sq, one_pow, mul_one]

theorem integerEulerCutDifference_binomial (F : ℕ → ℤ) (r j : ℕ) :
    integerEulerCutDifference F r j =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℤ) ^ k * (r.choose k : ℤ) * F (j + k) := by
  rw [integerEulerCutDifference, fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkr : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp only [nsmul_eq_mul, mul_one, zsmul_eq_mul, Int.cast_id, Nat.cast_id]
  rw [← mul_assoc, ← mul_assoc, integerEulerCutSign_cancel r k hkr]

theorem iteratedEulerCut_eq_difference_of_recurrence
    (c : ℕ → ℕ → ℤ)
    (hc : ∀ r j, c (r + 1) j = c r j - c r (j + 1)) (r j : ℕ) :
    c r j = integerEulerCutDifference (c 0) r j := by
  induction r generalizing j with
  | zero => exact (integerEulerCutDifference_zero (c 0) j).symm
  | succ r ih =>
      rw [hc, integerEulerCutDifference_succ, ih j, ih (j + 1)]

theorem iteratedEulerCut_binomial_of_recurrence
    (c : ℕ → ℕ → ℤ)
    (hc : ∀ r j, c (r + 1) j = c r j - c r (j + 1)) (r j : ℕ) :
    c r j =
      ∑ k ∈ Finset.range (r + 1), (-1 : ℤ) ^ k * (r.choose k : ℤ) * c 0 (j + k) := by
  rw [iteratedEulerCut_eq_difference_of_recurrence c hc, integerEulerCutDifference_binomial]

end MixedFujita
