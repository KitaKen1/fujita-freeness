/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalSliceCertificates

/-!
Write tau=a/b. Raise each shared product to the r*a-th power and choose
h=r*j*D*b. The common section degree is h*tau=r*j*D*a, and the initial
exponents normalize to tau times the previous slice targets. This is the
integer/rational and power-series calculation; geometric section degrees
and multiplicities still require the geometric Taylor-map connection.
-/

@[expose] public section

namespace MixedFujita

def equalityHeight (r j D b : ℕ) : ℕ := r * j * D * b

def equalitySectionDegree (r j D a : ℕ) : ℕ := r * j * D * a

theorem equalityHeight_pos {r j D b : ℕ}
    (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (hb : 0 < b) :
    0 < equalityHeight r j D b := by
  unfold equalityHeight
  positivity

theorem equalityHeight_mul_tau (r j D a : ℕ) {b : ℕ} (hb : 0 < b) :
    (equalityHeight r j D b : ℚ) * ((a : ℚ) / b) = equalitySectionDegree r j D a := by
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [equalityHeight, equalitySectionDegree, Nat.cast_mul]
  field_simp

theorem equality_scaled_exponent_coordinate {σ : Type*} (β : σ →₀ ℕ)
    {r j D b : ℕ} (a : ℕ) (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (hb : 0 < b)
    (i : σ) :
    (((r * a) • β) i : ℚ) / equalityHeight r j D b =
      ((a : ℚ) / b) * ((β i : ℚ) / ((D : ℚ) * j)) := by
  have hrq : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hj.ne'
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [equalityHeight, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_mul, Nat.cast_id]
  field_simp

theorem equality_scaled_slice_coordinate {n : ℕ} (β : Fin n →₀ ℕ)
    {r j D a b : ℕ} {δ : ℚ} (k l i : Fin n)
    (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hβ : (β i : ℚ) / ((D : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k l i) :
    (((r * a) • β) i : ℚ) / equalityHeight r j D b =
      1 + ((a : ℚ) / b) * δ *
        ((if i = k then (1 : ℚ) else 0) - (if i = l then (1 : ℚ) else 0)) := by
  rw [equality_scaled_exponent_coordinate β a hr hj hD hb, hβ]
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold rationalSliceTarget
  field_simp

theorem equality_scaled_exponent_totalDegree {n : ℕ} (β : Fin n →₀ ℕ)
    {r j D a b : ℕ} (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hβ : (∑ i, (β i : ℚ) / ((D : ℚ) * j)) = (n : ℚ) * ((b : ℚ) / a)) :
    (∑ i, ((r * a) • β) i) = n * equalityHeight r j D b := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hh : (equalityHeight r j D b : ℚ) ≠ 0 := by
    exact_mod_cast (equalityHeight_pos hr hj hD hb).ne'
  have hsum : (∑ i, ((((r * a) • β) i : ℚ) / equalityHeight r j D b)) = n := by
    simp_rw [equality_scaled_exponent_coordinate β a hr hj hD hb]
    rw [← Finset.mul_sum, hβ]
    field_simp
  rw [← Finset.sum_div] at hsum
  have h := (div_eq_iff hh).mp hsum
  exact_mod_cast h

theorem equality_slice_totalDegree {n : ℕ} (β : Fin n →₀ ℕ)
    {r j D a b : ℕ} {δ : ℚ} (k l : Fin n)
    (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hβ : ∀ i, (β i : ℚ) / ((D : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k l i) :
    (∑ i, ((r * a) • β) i) = n * equalityHeight r j D b := by
  apply equality_scaled_exponent_totalDegree β hr hj hD ha hb
  simp_rw [hβ]
  rw [rationalSliceTarget_sum]
  simp

theorem exists_arbitrarily_large_equalityHeight {j D b : ℕ}
    (hj : 0 < j) (hD : 0 < D) (hb : 0 < b) (M : ℕ) :
    ∃ r > 0, M < equalityHeight r j D b := by
  refine ⟨M + 1, by omega, ?_⟩
  have hbase : 0 < j * D * b := by positivity
  have hle : M + 1 ≤ (M + 1) * (j * D * b) := Nat.le_mul_of_pos_right _ hbase
  have heq : equalityHeight (M + 1) j D b = (M + 1) * (j * D * b) := by
    unfold equalityHeight
    ring
  rw [heq]
  omega

theorem equality_powerSeries_initialMonomial {σ K : Type*} [Field K]
    (order : MonomialOrder σ) {φ : MvPowerSeries σ K} {β : σ →₀ ℕ}
    (hφ : IsInitialMonomial order φ β) (r a : ℕ) :
    IsInitialMonomial order (φ ^ (r * a)) ((r * a) • β) :=
  initialMonomial_pow order hφ (r * a)

end MixedFujita
