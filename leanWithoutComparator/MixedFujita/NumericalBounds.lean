/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
Numerical implications at the end of Section 7. Geometric positivity,
multilinearity of intersection products, and the numerical freeness
criteria are separate unfinished dependencies.
-/

@[expose] public section

namespace MixedFujita

/-- Root-free form of the binomial estimate in uniform restriction growth. -/
theorem factorial_choose_lower_bound (r d : ℕ) :
    r ^ d ≤ d.factorial * (r + d).choose d := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact (Nat.pow_le_pow_left (Nat.le_succ r) d).trans
    (Nat.pow_succ_le_ascFactorial (r + 1) d)

/-- The numerical consequence of the independent-section count. -/
theorem restriction_count_power_bound (I D₀ r d : ℕ)
    (hcount : D₀ * (r + d).choose d ≤ I) :
    D₀ * r ^ d ≤ d.factorial * I := by
  calc
    D₀ * r ^ d ≤ D₀ * (d.factorial * (r + d).choose d) :=
      Nat.mul_le_mul_left D₀ (factorial_choose_lower_bound r d)
    _ = d.factorial * (D₀ * (r + d).choose d) := by ring
    _ ≤ d.factorial * I := Nat.mul_le_mul_left d.factorial hcount

/-- There are `s^d` ordered terms in the expansion; each is at least one. -/
theorem mixed_sum_ge_card_pow {ι : Type*} [Fintype ι]
    (d : ℕ) (w : (Fin d → ι) → ℤ) (hw : ∀ f, 1 ≤ w f) :
    (Fintype.card ι : ℤ) ^ d ≤ ∑ f, w f := by
  calc
    (Fintype.card ι : ℤ) ^ d = ∑ _f : Fin d → ι, (1 : ℤ) := by simp
    _ ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => hw f

/-- Numerical part of S-NF → mixed Fujita, with arbitrary dimension. -/
theorem mixed_sum_ge_fujita_bound {ι : Type*} [Fintype ι]
    (n d : ℕ) (hs : n + 1 ≤ Fintype.card ι)
    (w : (Fin d → ι) → ℤ) (hw : ∀ f, 1 ≤ w f) :
    ((n : ℤ) + 1) ^ d ≤ ∑ f, w f := by
  have hs' : (n : ℤ) + 1 ≤ Fintype.card ι := by exact_mod_cast hs
  exact (pow_le_pow_left₀ (by positivity) hs' d).trans (mixed_sum_ge_card_pow d w hw)

/-- The coefficient is strictly beyond the numerical threshold for every
integer in the asserted range, rather than only divisible integers. -/
theorem effective_coefficient_strict (n : ℕ) {a m : ℤ} {ε : ℝ}
    (hm : a + (n : ℤ) + 1 ≤ m) (hε : 0 < ε) :
    (n : ℝ) + 1 < (m : ℝ) - (a : ℝ) + ε := by
  have hm' : (a : ℝ) + (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- Positivity and integrality of the intersection number provide the final
strict intersection bound used before K-NF. -/
theorem effective_intersection_strict (n e : ℕ) (he : e ≠ 0)
    {a m z : ℤ} {ε : ℝ}
    (hm : a + (n : ℤ) + 1 ≤ m) (hε : 0 < ε) (hz : 1 ≤ z) :
    ((n : ℝ) + 1) ^ e < ((m : ℝ) - (a : ℝ) + ε) ^ e * (z : ℝ) := by
  have hc := effective_coefficient_strict n hm hε
  have hbase : 0 ≤ (n : ℝ) + 1 := by positivity
  have hp : ((n : ℝ) + 1) ^ e < ((m : ℝ) - (a : ℝ) + ε) ^ e :=
    pow_lt_pow_left₀ hc hbase he
  have hz' : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hx : 0 ≤ ((m : ℝ) - (a : ℝ) + ε) ^ e :=
    pow_nonneg (hbase.trans hc.le) e
  exact hp.trans_le (by nlinarith)

end MixedFujita
