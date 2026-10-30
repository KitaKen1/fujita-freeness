/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JacobianValuationBound
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
The SNC discrepancy inequality A(v) ≥ Σ_i v(x_i) for test valuations. Let ψ : K[[x]] → K[[z]] be
a K-algebra map and v_w the monomial valuation with weights w in the coordinates z, with log
discrepancy A(v) = Σ_j w_j + v_w(det J) for the Jacobian J_ij = ∂_j ψ(x_i). The Euler derivatives
z_j ∂_j do not lower v_w, so the matrix B = J · diag(z) with entries z_j ∂_j ψ(x_i) satisfies
v_w(B_ij) ≥ v_w(ψ(x_i)); expanding the determinant, v_w(det B) ≥ Σ_i v_w(ψ(x_i)), while
det B = det J · z_1 ⋯ z_n has v_w(det B) = v_w(det J) + Σ_j w_j. Hence A(v) ≥ Σ_i v(ψ(x_i)): the
pair (X, Σ_i {x_i = 0}) is log canonical along these test valuations, with equality for monomial
valuations in the coordinates x themselves. With boundary coefficients 1 - a_i on {x_i = 0} this
is r_F = Σ_i a_i v(x_i) ≤ A(v) - Σ_i (1 - a_i) v(x_i), the inequality r_F ≤ a_F of (28). For a
monomial ideal (x^β_ℓ) and an integer h with min_ℓ ⟨u, β_ℓ⟩ < h Σ_i u_i for every nonzero weight u,
some generator has v(ψ(x^β_ℓ)) < h A(v): the threshold of the monomial ideal exceeds 1/h along
every test valuation, the monomial case of (34).
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {σ K : Type*} [Field K]

/-- The Euler derivative z_j ∂_j does not lower the weighted order. -/
theorem weightedOrder_le_X_mul_pderiv (w : σ → ℕ) (j : σ) (g : MvPowerSeries σ K) :
    g.weightedOrder w ≤ (X j * pderiv j g).weightedOrder w := by
  apply le_weightedOrder
  intro d hd
  rw [coeff_X_mul_pderiv, coeff_eq_zero_of_lt_weightedOrder w hd, mul_zero]

variable [Fintype σ] [DecidableEq σ] (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)

/-- The SNC discrepancy inequality: Σ_i v(ψ(x_i)) ≤ Σ_j w_j + v(det J) = A(v). -/
theorem sum_weightedOrder_le_logDiscrepancy (w : σ → ℕ) :
    ∑ i, (ψ (X i)).weightedOrder w ≤
      ((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w := by
  set B := powerSeriesJacobian ψ * Matrix.diagonal (fun j => (X j : MvPowerSeries σ K)) with hB
  have hentry : ∀ i j, (ψ (X i)).weightedOrder w ≤ (B i j).weightedOrder w := by
    intro i j
    rw [hB, Matrix.mul_diagonal]
    simp only [powerSeriesJacobian, Matrix.of_apply]
    rw [mul_comm]
    exact weightedOrder_le_X_mul_pderiv w j _
  have hdet : ∑ i, (ψ (X i)).weightedOrder w ≤ B.det.weightedOrder w := by
    rw [Matrix.det_apply]
    apply le_weightedOrder_sum w
    intro π _
    have hsign : ∀ x : MvPowerSeries σ K,
        ((Equiv.Perm.sign π) • x).weightedOrder w = x.weightedOrder w := by
      intro x
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h
      · rw [h, one_smul]
      · rw [h, Units.neg_smul, one_smul, weightedOrder_neg]
    rw [hsign]
    calc ∑ i, (ψ (X i)).weightedOrder w = ∑ i, (ψ (X (π i))).weightedOrder w :=
          (Equiv.sum_comp π (fun i => (ψ (X i)).weightedOrder w)).symm
      _ ≤ ∑ i, (B (π i) i).weightedOrder w := Finset.sum_le_sum fun i _ => hentry (π i) i
      _ ≤ (∏ i, B (π i) i).weightedOrder w := le_weightedOrder_prod w _ _
  have hmul : B.det.weightedOrder w =
      (powerSeriesJacobian ψ).det.weightedOrder w + ((∑ j, w j : ℕ) : ℕ∞) := by
    rw [hB, Matrix.det_mul, Matrix.det_diagonal, weightedOrder_mul, weightedOrder_prod]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [X_def, weightedOrder_monomial_of_ne_zero w one_ne_zero, Finsupp.weight_single, one_smul]
  rw [hmul, add_comm] at hdet
  exact hdet

omit [DecidableEq σ] in
/-- Equality for monomial valuations in the coordinates x themselves. -/
theorem sum_weightedOrder_X (w : σ → ℕ) :
    ∑ i, (X i : MvPowerSeries σ K).weightedOrder w = ((∑ j, w j : ℕ) : ℕ∞) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  classical
  rw [X_def, weightedOrder_monomial_of_ne_zero w one_ne_zero, Finsupp.weight_single, one_smul]

omit [DecidableEq σ] in
/-- The value of a monomial: v(ψ(x^β)) = Σ_i β_i v(ψ(x_i)). -/
theorem weightedOrder_algHom_monomial (w : σ → ℕ) (β : σ →₀ ℕ) :
    (ψ (monomial β (1 : K))).weightedOrder w = ∑ i, β i • (ψ (X i)).weightedOrder w := by
  have hmono : (monomial β (1 : K) : MvPowerSeries σ K) = ∏ i, (X i) ^ (β i) := by
    simp only [X_pow_eq]
    rw [prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]
  rw [hmono, map_prod, weightedOrder_prod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow]
  induction β i with
  | zero => simp
  | succ k ih => rw [pow_succ, weightedOrder_mul, ih, succ_nsmul]

/-- The monomial case of (34): if min_ℓ ⟨u, β_ℓ⟩ < h Σ_i u_i for every nonzero weight u, then along
every test valuation some generator of the monomial ideal has v(ψ(x^β_ℓ)) < h A(v). -/
theorem exists_monomial_lt_logDiscrepancy {ι : Type*} [Nonempty ι] (β : ι → (σ →₀ ℕ)) (h : ℕ)
    (hh : 1 ≤ h) (hβ : ∀ u : σ → ℕ, u ≠ 0 → ∃ ℓ, ∑ i, u i * β ℓ i < h * ∑ i, u i)
    (hψ : ∀ i, ψ (X i) ≠ 0) (w : σ → ℕ) (hw : w ≠ 0) :
    ∃ ℓ, (ψ (monomial (β ℓ) (1 : K))).weightedOrder w <
      (h : ℕ∞) * (((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) := by
  set a : σ → ℕ := fun i => ((ψ (X i)).weightedOrder w).toNat with ha
  have hfin : ∀ i, ((ψ (X i)).weightedOrder w) = (a i : ℕ∞) := fun i =>
    ((ne_zero_iff_weightedOrder_finite w).mp (hψ i)).symm
  have hval : ∀ ℓ, (ψ (monomial (β ℓ) (1 : K))).weightedOrder w = ((∑ i, a i * β ℓ i : ℕ) : ℕ∞) := by
    intro ℓ
    rw [weightedOrder_algHom_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfin, nsmul_eq_mul, mul_comm]
  have hA := sum_weightedOrder_le_logDiscrepancy ψ w
  simp only [hfin] at hA
  have hwpos : 1 ≤ ∑ j, w j := by
    by_contra h0
    push Not at h0
    apply hw
    funext j
    have : w j ≤ ∑ j, w j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.zero_apply]
    omega
  by_cases ha0 : a = 0
  · obtain ⟨ℓ⟩ := ‹Nonempty ι›
    refine ⟨ℓ, ?_⟩
    rw [hval]
    simp only [ha0, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Nat.cast_zero]
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (h : ℕ∞) * ((∑ j, w j : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc (0 : ℕ∞) < 1 := by norm_num
      _ ≤ (h : ℕ∞) * ((∑ j, w j : ℕ) : ℕ∞) := by exact_mod_cast h1
      _ ≤ _ := by gcongr; exact le_self_add
  · obtain ⟨ℓ, hℓ⟩ := hβ a ha0
    refine ⟨ℓ, ?_⟩
    rw [hval]
    calc ((∑ i, a i * β ℓ i : ℕ) : ℕ∞) < ((h * ∑ i, a i : ℕ) : ℕ∞) := by exact_mod_cast hℓ
      _ = (h : ℕ∞) * ∑ i, (a i : ℕ∞) := by push_cast; rfl
      _ ≤ _ := by gcongr

end MixedFujita
