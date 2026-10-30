/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PowerSeriesExponents
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Tactic.Ring

/-!
Clear a given finite rational convex combination by an explicit product of
denominators, then take actual products of power series with the prescribed
initial exponents. Existence of the required convex-hull slice and geometric
section multiplication are separate dependencies.
-/

@[expose] public section

namespace MixedFujita

open scoped NNRat

def rationalProductDenominator {ι : Type*} (E : Finset ι) (q : ι → ℚ≥0) : ℕ :=
  ∏ i ∈ E, (q i).den

def clearedRationalMultiplicity {ι : Type*} (E : Finset ι) (q : ι → ℚ≥0) (i : ι) : ℕ :=
  (rationalProductDenominator E q / (q i).den) * (q i).num

theorem rationalProductDenominator_pos {ι : Type*} (E : Finset ι) (q : ι → ℚ≥0) :
    0 < rationalProductDenominator E q := by
  exact Finset.prod_pos fun _ _ => NNRat.den_pos _

theorem clearedRationalMultiplicity_spec {ι : Type*} (E : Finset ι) (q : ι → ℚ≥0)
    {i : ι} (hi : i ∈ E) :
    (clearedRationalMultiplicity E q i : ℚ≥0) = (rationalProductDenominator E q : ℚ≥0) * q i := by
  have hdiv : (q i).den ∣ rationalProductDenominator E q := Finset.dvd_prod_of_mem _ hi
  have hcancel := Nat.div_mul_cancel hdiv
  unfold clearedRationalMultiplicity
  rw [Nat.cast_mul, ← NNRat.den_mul_eq_num (q i)]
  rw [← mul_assoc, ← Nat.cast_mul, hcancel]

theorem clearedRationalMultiplicity_sum {ι : Type*} (E : Finset ι) (q : ι → ℚ≥0)
    (hq : (∑ i ∈ E, q i) = 1) :
    (∑ i ∈ E, clearedRationalMultiplicity E q i) = rationalProductDenominator E q := by
  have h : ((∑ i ∈ E, clearedRationalMultiplicity E q i) : ℚ≥0) =
      (rationalProductDenominator E q : ℚ≥0) := by
    calc
      _ = ∑ i ∈ E, (rationalProductDenominator E q : ℚ≥0) * q i :=
        Finset.sum_congr rfl fun i hi => clearedRationalMultiplicity_spec E q hi
      _ = _ := by rw [← Finset.mul_sum, hq, mul_one]
  exact_mod_cast h

/-- The cleared exponent represents the original rational combination in
every coordinate, scaled by the same positive integer denominator. -/
theorem clearedRational_exponent_coordinate {ι σ : Type*}
    (E : Finset ι) (q : ι → ℚ≥0) (p : ι → σ →₀ ℕ) (s : σ) :
    ((∑ i ∈ E, clearedRationalMultiplicity E q i • p i) s : ℚ≥0) =
      (rationalProductDenominator E q : ℚ≥0) * (∑ i ∈ E, q i * (p i s : ℚ≥0)) := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [clearedRationalMultiplicity_spec E q hi]
  ring

variable {σ K : Type*} [Field K]

theorem initialMonomial_one (m : MonomialOrder σ) :
    IsInitialMonomial m (1 : MvPowerSeries σ K) 0 := by
  constructor
  · simp
  · intro p hp
    have h : ¬ m.toSyn p < 0 := not_lt_of_ge (m.zero_le _)
    exact False.elim (h (by simpa only [map_zero] using hp))

theorem initialMonomial_pow (m : MonomialOrder σ)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ} (hp : IsInitialMonomial m φ p) (k : ℕ) :
    IsInitialMonomial m (φ ^ k) (k • p) := by
  induction k with
  | zero => simpa only [pow_zero, zero_nsmul] using initialMonomial_one m
  | succ k ih =>
    simpa only [pow_succ, add_nsmul, one_nsmul] using initialMonomial_mul m ih hp

theorem initialMonomial_prod {ι : Type*} (m : MonomialOrder σ) (E : Finset ι)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) :
    IsInitialMonomial m (∏ i ∈ E, φ i) (∑ i ∈ E, p i) := by
  classical
  revert hφ
  induction E using Finset.induction_on with
  | empty => intro _; simpa only [Finset.prod_empty, Finset.sum_empty] using initialMonomial_one m
  | @insert i E hi ih =>
    intro hφ
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact initialMonomial_mul m (hφ i (Finset.mem_insert_self _ _))
      (ih fun a ha => hφ a (Finset.mem_insert_of_mem ha))

theorem initialMonomial_weighted_prod {ι : Type*} (m : MonomialOrder σ) (E : Finset ι)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ) (k : ι → ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) :
    IsInitialMonomial m (∏ i ∈ E, (φ i) ^ k i) (∑ i ∈ E, k i • p i) :=
  initialMonomial_prod m E (fun i => (φ i) ^ k i) (fun i => k i • p i)
    (fun i hi => initialMonomial_pow m (hφ i hi) (k i))

/-- A given rational combination is realized by a nonzero actual product. -/
theorem clearedRational_product_initialMonomial {ι : Type*} (m : MonomialOrder σ)
    (E : Finset ι) (q : ι → ℚ≥0) (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) :
    IsInitialMonomial m (∏ i ∈ E, (φ i) ^ clearedRationalMultiplicity E q i)
      (∑ i ∈ E, clearedRationalMultiplicity E q i • p i) :=
  initialMonomial_weighted_prod m E φ p (clearedRationalMultiplicity E q) hφ

theorem clearedRational_product_ne_zero {ι : Type*} (m : MonomialOrder σ)
    (E : Finset ι) (q : ι → ℚ≥0) (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) :
    (∏ i ∈ E, (φ i) ^ clearedRationalMultiplicity E q i) ≠ 0 := by
  have h := clearedRational_product_initialMonomial m E q φ p hφ
  intro hzero
  exact h.1 (by rw [hzero]; simp)

end MixedFujita
