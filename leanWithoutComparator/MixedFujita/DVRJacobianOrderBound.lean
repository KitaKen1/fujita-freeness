/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianRankOneDivisibility

/-!
The geometric Jacobian inequality is reduced directly to the actual DVR.
For f_i = u_i * π^m_i, the scaled logarithmic derivative matrix is π*A plus
a rank-one matrix in the direction dπ. Its determinant contains n-1 powers
of π. Cancelling π^n proves that π^(sum m_i - 1) divides the actual derivative
determinant. The resulting DVR order inequality does not use a formal-test-
valuation identification.
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

/-- The scaled logarithmic derivative of a unit times a power has one common direction dπ. -/
theorem derivation_unit_pow_scaled {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (D : Derivation K R R) (π : R) (u : Rˣ) (m : ℕ) :
    π * D ((u : R) * π ^ m) =
      ((u : R) * π ^ m) *
        (π * ((u⁻¹ : Rˣ) : R) * D (u : R) + (m : R) * D π) := by
  have hu : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hp : π * (m : R) * π ^ (m - 1) = (m : R) * π ^ m := by
    cases m with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_sub_one, pow_succ]
      ring
  rw [D.leibniz, D.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  linear_combination (u : R) * D π * hp - π * π ^ m * D (u : R) * hu

/-- Powers forced by the common differential direction give actual determinant divisibility. -/
theorem derivation_unit_pow_jacobian_dvd {K R ι : Type*}
    [CommRing K] [CommRing R] [IsDomain R] [Algebra K R] [Fintype ι] [DecidableEq ι]
    (D : ι → Derivation K R R) (π : R) (hπ : π ≠ 0) (u : ι → Rˣ) (m : ι → ℕ) :
    π ^ ((∑ i, m i) - 1) ∣
      (Matrix.of fun i j => D j ((u i : R) * π ^ m i)).det := by
  classical
  let f := fun i => (u i : R) * π ^ m i
  let A : Matrix ι ι R := Matrix.of fun i j => (((u i)⁻¹ : Rˣ) : R) * D j (u i : R)
  let M : Matrix ι ι R := π • A + Matrix.vecMulVec (fun i => (m i : R)) (fun j => D j π)
  let J : Matrix ι ι R := Matrix.of fun i j => D j (f i)
  have hmat : π • J = Matrix.diagonal f * M := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, Matrix.add_apply,
      Matrix.vecMulVec_apply, Matrix.of_apply, A, M, J, f]
    simpa only [mul_assoc] using derivation_unit_pow_scaled (D j) π (u i) (m i)
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hprod : ∏ i, f i = (∏ i, (u i : R)) * π ^ (∑ i, m i) := by
    simp only [f, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hprod] at hdet
  obtain ⟨q, hq⟩ := matrix_scalar_rank_one_det_dvd π A (fun i => (m i : R)) (fun j => D j π)
  change M.det = π ^ (Fintype.card ι - 1) * q at hq
  rw [hq] at hdet
  by_cases hsum : ∑ i, m i = 0
  · simp only [hsum, Nat.zero_sub, pow_zero, one_dvd]
  · obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
    have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    have he : (∑ i, m i) + (Fintype.card ι - 1) =
        Fintype.card ι + ((∑ i, m i) - 1) := by omega
    refine ⟨(∏ i, (u i : R)) * q, ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero (Fintype.card ι) hπ)
    change π ^ Fintype.card ι * J.det = _
    calc
      _ = ((∏ i, (u i : R)) * π ^ (∑ i, m i)) *
          (π ^ (Fintype.card ι - 1) * q) := hdet
      _ = π ^ ((∑ i, m i) + (Fintype.card ι - 1)) *
          ((∏ i, (u i : R)) * q) := by rw [pow_add]; ring
      _ = _ := by rw [he, pow_add]; ring

/-- On an actual DVR, the sum of orders of nonzero functions is at most one plus
the order of their derivative determinant, for arbitrary regular derivations. -/
theorem dvr_derivation_jacobian_order_bound {K R ι : Type*}
    [CommRing K] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra K R]
    [Fintype ι] [DecidableEq ι] (D : ι → Derivation K R R)
    (f : ι → R) (hf : ∀ i, f i ≠ 0) :
    ∑ i, Ring.ord R (f i) ≤
      1 + Ring.ord R (Matrix.of fun i j => D j (f i)).det := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  choose m u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hf i) hπ
  have hdiv := derivation_unit_pow_jacobian_dvd D π hπ.ne_zero u m
  simp only [← hu] at hdiv
  have hord := Ring.ord_le_ord_of_dvd hdiv
  rw [Ring.ord_eq_addVal, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer hπ, nsmul_eq_mul, mul_one] at hord
  have hfi : ∀ i, Ring.ord R (f i) = (m i : ℕ∞) := by
    intro i
    rw [hu i, Ring.ord_eq_addVal, AddValuation.map_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, AddValuation.map_pow,
      IsDiscreteValuationRing.addVal_uniformizer hπ]
    simp
  simp_rw [hfi]
  rw [← Nat.cast_sum]
  by_cases hsum : ∑ i, m i = 0
  · simp [hsum]
  · have he : ∑ i, m i = 1 + ((∑ i, m i) - 1) := by omega
    rw [he, Nat.cast_add, Nat.cast_one]
    simpa only [add_comm] using add_le_add_left hord 1

end MixedFujita
