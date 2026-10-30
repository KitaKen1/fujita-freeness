/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricExtraction
public import MixedFujita.JacobianValuationBound
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
The log discrepancy of the extracted toric divisor (§6.1). For the monomial substitution
ψ : x_i ↦ u^(M_i), the Jacobian satisfies J_ij u_j = M_ij u^(M_i), so J · diag(u) = diag(u^(M_i)) · M
and det J · u^1 = det M · u^(Σ_i M_i). When every column sum of M is positive this is
det J = det M · u^κ with κ_j = Σ_i M_ij - 1. The log discrepancy Σ_j w_j + v_w(det J) of the
monomial valuation v_w on the chart is then Σ_i (M w)_i, the log discrepancy of v_{Mw} = v_w ∘ ψ
in the original coordinates: the chart preserves log discrepancies. A blow-up chart has
determinant 1 by the matrix determinant lemma, so composites of charts do too; for the ray a of the
toric extraction, A(v_a) = Σ_i a_i = g Σ_i M_ik = g A(ord_E). The blow-up of a point is the chart
with S = σ, where ord_E is the order (multiplicity) and A(ord_E) = |σ|.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
/-- ∂_j u^r · u_j = r_j u^r. -/
theorem pderiv_monomial_mul_X (r : σ →₀ ℕ) (j : σ) :
    pderiv j (monomial r (1 : K)) * X j = monomial r (r j : K) := by
  by_cases hr : r j = 0
  · have h0 : pderiv j (monomial r (1 : K)) = 0 := by
      rw [← MvPolynomial.coe_monomial, pderiv_coe, MvPolynomial.pderiv_monomial, hr,
        Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero, MvPolynomial.coe_zero]
    rw [h0, zero_mul, hr, Nat.cast_zero, map_zero]
  · have hle : Finsupp.single j 1 ≤ r := by
      intro l
      rw [Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · exact Nat.zero_le _
    rw [← MvPolynomial.coe_monomial, pderiv_coe, MvPolynomial.pderiv_monomial, one_mul,
      ← MvPolynomial.coe_X, ← MvPolynomial.coe_mul, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
      mul_one, tsub_add_cancel_of_le hle, MvPolynomial.coe_monomial]

variable {M : Matrix σ σ ℕ} (hrow : ∀ i, ∃ j, M i j ≠ 0)

/-- The Jacobian of the monomial substitution times diag(u). -/
theorem jacobian_monomialSubst_mul_diagonal :
    powerSeriesJacobian (substAlgHom (R := K) (hasSubst_monomialSubstVars hrow)) *
        Matrix.diagonal (fun j => (X j : MvPowerSeries σ K)) =
      Matrix.diagonal (fun i => monomial (matrixRowExponent M i) (1 : K)) *
        (C.mapMatrix (M.map (Nat.cast : ℕ → K))) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [powerSeriesJacobian, Matrix.of_apply, substAlgHom_X, monomialSubstVars,
    pderiv_monomial_mul_X, RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [mul_comm, ← smul_eq_C_mul, ← map_smul, smul_eq_mul, mul_one]
  simp [matrixRowExponent]

/-- det J · u^1 = det M · u^(Σ_i M_i). -/
theorem det_jacobian_monomialSubst_mul :
    (powerSeriesJacobian (substAlgHom (R := K) (hasSubst_monomialSubstVars hrow))).det *
        monomial (∑ j, Finsupp.single j 1) (1 : K) =
      C (M.map (Nat.cast : ℕ → K)).det * monomial (∑ i, matrixRowExponent M i) 1 := by
  have h := congrArg Matrix.det (jacobian_monomialSubst_mul_diagonal (K := K) hrow)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    ← RingHom.map_det] at h
  have hX : (∏ j, (X j : MvPowerSeries σ K)) = monomial (∑ j, Finsupp.single j 1) 1 := by
    have := prod_monomial (R := K) (fun j : σ => Finsupp.single j 1) (fun _ => (1 : K))
      Finset.univ
    rw [Finset.prod_const_one] at this
    rw [← this]
    simp only [X_def]
  have hu : (∏ i, monomial (matrixRowExponent M i) (1 : K)) =
      monomial (∑ i, matrixRowExponent M i) 1 := by
    rw [prod_monomial, Finset.prod_const_one]
  rw [hX, hu] at h
  rw [h, mul_comm]

/-- The exponent κ_j = Σ_i M_ij - 1 of the Jacobian determinant. -/
noncomputable def jacobianExponent (M : Matrix σ σ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => (∑ i, M i j) - 1

omit [DecidableEq σ] in
theorem sum_matrixRowExponent_apply (j : σ) :
    (∑ i, matrixRowExponent M i) j = ∑ i, M i j := by
  simp only [Finsupp.coe_finsetSum, matrixRowExponent, Finsupp.coe_equivFunOnFinite_symm]
  exact Finset.sum_apply j Finset.univ (fun i => M i)

/-- det J = det M · u^κ when every column sum of M is positive. -/
theorem det_jacobian_monomialSubst (hcol : ∀ j, 1 ≤ ∑ i, M i j) :
    (powerSeriesJacobian (substAlgHom (R := K) (hasSubst_monomialSubstVars hrow))).det =
      C (M.map (Nat.cast : ℕ → K)).det * monomial (jacobianExponent M) 1 := by
  have h := det_jacobian_monomialSubst_mul (K := K) hrow
  have hsplit : (∑ i, matrixRowExponent M i) = jacobianExponent M + ∑ j, Finsupp.single j 1 := by
    ext j
    rw [Finsupp.add_apply, sum_matrixRowExponent_apply]
    have hone : (∑ x : σ, Finsupp.single x 1) j = 1 := by
      rw [Finsupp.coe_finsetSum, Finset.sum_apply]
      simp [Finsupp.single_apply]
    rw [hone]
    simp only [jacobianExponent, Finsupp.coe_equivFunOnFinite_symm]
    have := hcol j
    omega
  have h2 : C (M.map (Nat.cast : ℕ → K)).det *
      monomial (jacobianExponent M + ∑ j, Finsupp.single j 1) (1 : K) =
        (C (M.map (Nat.cast : ℕ → K)).det * monomial (jacobianExponent M) 1) *
          monomial (∑ j, Finsupp.single j 1) 1 := by
    rw [mul_assoc, monomial_mul_monomial, mul_one]
  rw [hsplit, h2] at h
  have hne : (monomial (∑ j : σ, Finsupp.single j 1) (1 : K) : MvPowerSeries σ K) ≠ 0 := by
    intro h0
    have := congrArg (coeff (∑ j : σ, Finsupp.single j 1)) h0
    simp at this
  exact mul_right_cancel₀ hne h

/-- The chart preserves log discrepancies: Σ_j w_j + v_w(det J) = Σ_i (M w)_i. -/
theorem logDiscrepancy_monomialSubst (hcol : ∀ j, 1 ≤ ∑ i, M i j)
    (hdet : (M.map (Nat.cast : ℕ → K)).det ≠ 0) (w : σ → ℕ) :
    ((∑ j, w j : ℕ) : ℕ∞) +
        (powerSeriesJacobian (substAlgHom (R := K) (hasSubst_monomialSubstVars hrow))).det.weightedOrder
          w = ((∑ i, M.mulVec w i : ℕ) : ℕ∞) := by
  rw [det_jacobian_monomialSubst hrow hcol, ← smul_eq_C_mul, ← map_smul, smul_eq_mul, mul_one,
    weightedOrder_monomial_of_ne_zero _ hdet]
  norm_cast
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [jacobianExponent, Finsupp.coe_equivFunOnFinite_symm, smul_eq_mul, Matrix.mulVec,
    dotProduct]
  rw [← Finset.sum_add_distrib, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hcol j
  rw [← Finset.sum_mul]
  calc w j + ((∑ i, M i j) - 1) * w j = (1 + ((∑ i, M i j) - 1)) * w j := by ring
    _ = (∑ i, M i j) * w j := by congr 1; omega

/-- A blow-up chart has determinant 1. -/
theorem det_blowupChartMatrix (S : Finset σ) (k : σ) :
    ((blowupChartMatrix S k).map (Nat.cast : ℕ → K)).det = 1 := by
  have hE : (blowupChartMatrix S k).map (Nat.cast : ℕ → K) =
      1 + Matrix.replicateCol Unit (fun i => if i ∈ S ∧ i ≠ k then (1 : K) else 0) *
        Matrix.replicateRow Unit (fun l => if l = k then (1 : K) else 0) := by
    ext i l
    simp only [blowupChartMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply,
      Finset.univ_unique, Finset.sum_singleton]
    by_cases hil : i = l <;> by_cases hlk : l = k <;> by_cases hi : i ∈ S ∧ i ≠ k <;>
      simp_all
  rw [hE, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, add_eq_left]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = k <;> simp [hx]

theorem det_toricChartProduct (L : List (Finset σ × σ)) :
    ((toricChartProduct L).map (Nat.cast : ℕ → K)).det = 1 := by
  induction L with
  | nil => simp [toricChartProduct]
  | cons p L ih =>
    have hmap : (toricChartProduct (p :: L)).map (Nat.cast : ℕ → K) =
        (blowupChartMatrix p.1 p.2).map (Nat.cast : ℕ → K) *
          (toricChartProduct L).map (Nat.cast : ℕ → K) := by
      rw [toricChartProduct_cons]
      exact Matrix.map_mul (f := Nat.castRingHom K)
    rw [hmap, Matrix.det_mul, det_blowupChartMatrix, ih, mul_one]

theorem one_le_toricChartProduct_colSum (L : List (Finset σ × σ)) (j : σ) :
    1 ≤ ∑ i, toricChartProduct L i j :=
  (one_le_toricChartProduct_diag L j).trans
    (Finset.single_le_sum (f := fun i => toricChartProduct L i j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j))

/-- The extracted divisor u_k = 0 of a composite of blow-up charts has log discrepancy
Σ_i M_ik over the original coordinates. -/
theorem logDiscrepancy_toricChart (L : List (Finset σ × σ)) (k : σ) :
    ((∑ j, (Pi.single k 1 : σ → ℕ) j : ℕ) : ℕ∞) +
        (powerSeriesJacobian (substAlgHom (R := K)
          (hasSubst_monomialSubstVars (toricChartProduct_row_ne_zero L)))).det.weightedOrder
          (Pi.single k 1) = ((∑ i, toricChartProduct L i k : ℕ) : ℕ∞) := by
  rw [logDiscrepancy_monomialSubst (toricChartProduct_row_ne_zero L)
    (one_le_toricChartProduct_colSum L) (by rw [det_toricChartProduct]; exact one_ne_zero)]
  congr 2
  funext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The blow-up of a point: for the chart with S = σ, the order along u_k = 0 after the
substitution is the order of f, and the exceptional divisor has log discrepancy |σ|. -/
theorem pointBlowup_order (k : σ) (f : MvPowerSeries σ K) :
    (subst (monomialSubstVars (K := K) (toricChartProduct [(Finset.univ, k)])) f).weightedOrder
        (Pi.single k 1) = f.order ∧
      ∑ i, toricChartProduct [(Finset.univ, k)] i k = Fintype.card σ := by
  have hcol : ∀ i, toricChartProduct [(Finset.univ, k)] i k = 1 := by
    intro i
    simp only [toricChartProduct, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, blowupChartMatrix, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
      Finset.mem_univ, true_and]
    by_cases hik : i = k <;> simp [hik]
  refine ⟨?_, by simp [hcol]⟩
  rw [weightedOrder_subst_monomialSubstVars (toricChartProduct_row_ne_zero _)
    (monomialImageExponent_toricChartProduct_injective _)]
  have hw : (toricChartProduct [(Finset.univ, k)]).mulVec (Pi.single k 1) = fun _ => 1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol]
  rw [hw]
  rfl

end MixedFujita
