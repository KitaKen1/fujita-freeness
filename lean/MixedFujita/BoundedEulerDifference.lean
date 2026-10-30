/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IteratedEulerDifference
import Lean.Elab.Tactic.Omega

/-!
Only the finite triangle r+j <= N is needed to compute N Cartier cuts.
No recurrence, sheaf, or cut outside that triangle is required.
-/

@[expose] public section
namespace MixedFujita

theorem boundedEulerCut_eq_difference
    (N : ℕ) (c : ℕ → ℕ → ℤ)
    (hc : ∀ r j, r + j < N → c (r + 1) j = c r j - c r (j + 1))
    (r j : ℕ) (hrj : r + j ≤ N) :
    c r j = integerEulerCutDifference (c 0) r j := by
  induction r generalizing j with
  | zero => exact (integerEulerCutDifference_zero (c 0) j).symm
  | succ r ih =>
    rw [hc r j (by omega), integerEulerCutDifference_succ,
      ih j (by omega), ih (j + 1) (by omega)]

theorem boundedEulerCut_binomial
    (N : ℕ) (c : ℕ → ℕ → ℤ)
    (hc : ∀ r j, r + j < N → c (r + 1) j = c r j - c r (j + 1))
    (r j : ℕ) (hrj : r + j ≤ N) :
    c r j = ∑ k ∈ Finset.range (r + 1),
      (-1 : ℤ) ^ k * (r.choose k : ℤ) * c 0 (j + k) := by
  rw [boundedEulerCut_eq_difference N c hc r j hrj,
    integerEulerCutDifference_binomial]

theorem boundedEulerCut_difference_binomial
    (N : ℕ) (c d : ℕ → ℕ → ℤ)
    (hc : ∀ r j, r + j < N → c (r + 1) j = c r j - c r (j + 1))
    (hd : ∀ r j, r + j < N → d (r + 1) j = d r j - d r (j + 1)) :
    c N 0 - d N 0 = ∑ k ∈ Finset.range (N + 1),
      (-1 : ℤ) ^ k * (N.choose k : ℤ) * (c 0 k - d 0 k) := by
  rw [boundedEulerCut_binomial N c hc N 0 (by omega),
    boundedEulerCut_binomial N d hd N 0 (by omega), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.zero_add, mul_sub]

end MixedFujita
