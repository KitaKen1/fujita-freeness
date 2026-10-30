/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
The elementary part of lct ≥ 1/mult for monomial valuations in coordinates. For
nonnegative integer weights w, the weighted order of a nonzero power series is at
most (Σ w_i) times its order: a coefficient of total degree equal to the order has
weight at most (Σ w) times that degree. In regular coordinates at a smooth point
Σ w_i is the log discrepancy of the monomial valuation with weights w, so this is
v(f) ≤ A(v) mult(f) for these valuations. Quasi-monomial valuations on other
models and their discrepancies are not treated here.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries Finset

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

theorem weight_le_weightSum_mul_degree (w : σ → ℕ) (p : σ →₀ ℕ) :
    Finsupp.weight w p ≤ (∑ i, w i) * p.degree := by
  rw [Finsupp.weight_apply, Finsupp.degree_eq_sum, Finsupp.sum_fintype _ _ (by simp)]
  calc ∑ i, p i • w i ≤ ∑ i, p i * ∑ j, w j := by
        apply sum_le_sum
        intro i _
        rw [smul_eq_mul]
        exact Nat.mul_le_mul_left _ (single_le_sum (fun j _ => Nat.zero_le (w j)) (mem_univ i))
    _ = (∑ j, w j) * ∑ i, p i := by rw [← sum_mul, mul_comm]

/-- For a nonzero power series, v_w(f) ≤ (Σ w) · ord(f). -/
theorem weightedOrder_le_weightSum_mul_order (w : σ → ℕ) {f : MvPowerSeries σ R} (hf : f ≠ 0) :
    f.weightedOrder w ≤ ((∑ i, w i) * f.order.toNat : ℕ) := by
  have hfin : (f.order.toNat : ℕ∞) = f.order := by
    apply ENat.natCast_toNat
    rwa [ne_eq, order_eq_top_iff]
  obtain ⟨p, hp, hdeg⟩ := exists_coeff_ne_zero_and_order hfin
  have hdeg' : p.degree = f.order.toNat := by
    have h : (p.degree : ℕ∞) = (f.order.toNat : ℕ∞) := hdeg.trans hfin.symm
    exact_mod_cast h
  calc f.weightedOrder w ≤ (Finsupp.weight w p : ℕ∞) := weightedOrder_le w hp
    _ ≤ ((∑ i, w i) * f.order.toNat : ℕ) := by
        rw [← hdeg']
        exact_mod_cast weight_le_weightSum_mul_degree w p

end MixedFujita
