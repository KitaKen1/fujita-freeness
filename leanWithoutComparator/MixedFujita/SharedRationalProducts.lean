/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalSectionProducts
public import Mathlib.Algebra.BigOperators.Field

/-!
One denominator for finitely many rational combinations. The constructed
products have one common total multiplicity and the expected initial
exponents. Geometric section spaces and their multiplication remain separate.
-/

@[expose] public section

namespace MixedFujita

def sharedRationalDenominator {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) : ℕ :=
  ∏ l, rationalProductDenominator E (q l)

def sharedRationalMultiplicity {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (l : L) (i : ι) : ℕ :=
  (sharedRationalDenominator E q / rationalProductDenominator E (q l)) *
    clearedRationalMultiplicity E (q l) i

theorem sharedRationalDenominator_pos {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) : 0 < sharedRationalDenominator E q := by
  exact Finset.prod_pos fun l _ => rationalProductDenominator_pos E (q l)

theorem rationalProductDenominator_dvd_shared {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (l : L) :
    rationalProductDenominator E (q l) ∣ sharedRationalDenominator E q :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ l)

theorem sharedRationalMultiplicity_spec {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (l : L) {i : ι} (hi : i ∈ E) :
    (sharedRationalMultiplicity E q l i : ℚ≥0) =
      (sharedRationalDenominator E q : ℚ≥0) * q l i := by
  unfold sharedRationalMultiplicity
  rw [Nat.cast_mul, clearedRationalMultiplicity_spec E (q l) hi,
    ← mul_assoc, ← Nat.cast_mul,
    Nat.div_mul_cancel (rationalProductDenominator_dvd_shared E q l)]

theorem sharedRationalMultiplicity_sum {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (l : L) (hq : (∑ i ∈ E, q l i) = 1) :
    (∑ i ∈ E, sharedRationalMultiplicity E q l i) = sharedRationalDenominator E q := by
  unfold sharedRationalMultiplicity
  rw [← Finset.mul_sum, clearedRationalMultiplicity_sum E (q l) hq,
    Nat.div_mul_cancel (rationalProductDenominator_dvd_shared E q l)]

theorem sharedRational_exponent_coordinate {ι L σ : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (p : ι → σ →₀ ℕ) (l : L) (s : σ) :
    ((∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) s : ℚ≥0) =
      (sharedRationalDenominator E q : ℚ≥0) * (∑ i ∈ E, q l i * (p i s : ℚ≥0)) := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sharedRationalMultiplicity_spec E q l hi]
  ring

theorem sharedRationalMultiplicity_spec_rat {ι L : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (l : L) {i : ι} (hi : i ∈ E) :
    (sharedRationalMultiplicity E q l i : ℚ) =
      (sharedRationalDenominator E q : ℚ) * (q l i : ℚ) := by
  exact_mod_cast sharedRationalMultiplicity_spec E q l hi

theorem sharedRational_exponent_coordinate_rat {ι L σ : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (p : ι → σ →₀ ℕ) (l : L) (s : σ) :
    ((∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) s : ℚ) =
      (sharedRationalDenominator E q : ℚ) * (∑ i ∈ E, (q l i : ℚ) * (p i s : ℚ)) := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_id]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sharedRationalMultiplicity_spec_rat E q l hi]
  ring

/-- The initial exponents of the shared-degree products realize every given
rational target after normalization by the same positive degree j*D. -/
theorem sharedRational_normalized_exponent {ι L σ : Type*} [Fintype L]
    (E : Finset ι) (q : L → ι → ℚ≥0) (p : ι → σ →₀ ℕ)
    (x : L → σ → ℚ) {j : ℕ} (hj : 0 < j)
    (hcomb : ∀ l, (∑ i ∈ E, (q l i : ℚ) • (fun s => (p i s : ℚ) / j)) = x l)
    (l : L) (s : σ) :
    ((∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) s : ℚ) /
      ((sharedRationalDenominator E q : ℚ) * j) = x l s := by
  have hD : (sharedRationalDenominator E q : ℚ) ≠ 0 := by
    exact_mod_cast (sharedRationalDenominator_pos E q).ne'
  have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
  have h := congrFun (hcomb l) s
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← mul_div_assoc,
    ← Finset.sum_div] at h
  rw [sharedRational_exponent_coordinate_rat]
  calc
    _ = (∑ i ∈ E, (q l i : ℚ) * (p i s : ℚ)) / j := by field_simp
    _ = _ := h

theorem sharedRational_product_initialMonomial {ι L σ K : Type*} [Fintype L] [Field K]
    (m : MonomialOrder σ) (E : Finset ι) (q : L → ι → ℚ≥0)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) (l : L) :
    IsInitialMonomial m (∏ i ∈ E, (φ i) ^ sharedRationalMultiplicity E q l i)
      (∑ i ∈ E, sharedRationalMultiplicity E q l i • p i) :=
  initialMonomial_weighted_prod m E φ p (sharedRationalMultiplicity E q l) hφ

theorem sharedRational_product_ne_zero {ι L σ K : Type*} [Fintype L] [Field K]
    (m : MonomialOrder σ) (E : Finset ι) (q : L → ι → ℚ≥0)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hφ : ∀ i ∈ E, IsInitialMonomial m (φ i) (p i)) (l : L) :
    (∏ i ∈ E, (φ i) ^ sharedRationalMultiplicity E q l i) ≠ 0 := by
  have h := sharedRational_product_initialMonomial m E q φ p hφ l
  intro hzero
  exact h.1 (by rw [hzero]; simp)

end MixedFujita
