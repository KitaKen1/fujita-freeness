/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The finite weighted convexity step (convex-growth), Section 4.
All weights may vary with the slice. The geometric slice bounds are inputs. -/

@[expose] public section

namespace MixedFujita

theorem power_increment_lower_bound (n : ℕ) {x r : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r) :
    x ^ (n + 1) + (n + 1 : ℝ) * r * x ^ n ≤ (x + r) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (add_nonneg hx hr)
    have hnonneg : 0 ≤ (n + 1 : ℝ) * r * r * x ^ n := by positivity
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] at h ⊢
    nlinarith

theorem weighted_power_growth {ι : Type*} (s : Finset ι) (n : ℕ)
    (w x y : ι → ℝ) {r : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i) (hr : 0 ≤ r)
    (hgrowth : ∀ i ∈ s, x i + r ≤ y i) :
    (∑ i ∈ s, w i * x i ^ (n + 1)) +
      (n + 1 : ℝ) * r * (∑ i ∈ s, w i * x i ^ n) ≤
        ∑ i ∈ s, w i * y i ^ (n + 1) := by
  calc
    _ = ∑ i ∈ s, w i * (x i ^ (n + 1) + (n + 1 : ℝ) * r * x i ^ n) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      exact (power_increment_lower_bound n (hx i hi) hr).trans
        (pow_le_pow_left₀ (add_nonneg (hx i hi) hr) (hgrowth i hi) (n + 1))

end MixedFujita
