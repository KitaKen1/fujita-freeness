/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartThreshold
public import MixedFujita.HomogeneousDegeneration

/-!
The threshold condition (34) is invariant under diagonal changes of coordinates and nonzero
scalars (§8, the nonzero fibres of the degeneration of Lemma 3).

Let g be a form of degree D and g_t(x) = g(t^w_1 x_1, …, t^w_n x_n) with t ≠ 0. In the chart
x_k = 1 at a point p, g_t becomes (t^w_k)^D times the image of g in the same chart at the point
μ p, μ_i = t^(w_i - w_k), under the rescaling y_i ↦ μ_i y_i of the chart coordinates. A test
valuation ψ at p composed with this rescaling is a test valuation at μ p with the same weights;
its Jacobian matrix is the one of ψ with the rows multiplied by the units μ_i, so its determinant
is still nonzero and the log discrepancy is unchanged. Hence the condition for the forms g_ℓ
gives the condition for their diagonal transforms, and since the transform by t⁻¹ undoes the one
by t, the two conditions are equivalent. Multiplying the forms by nonzero constants does not change the condition either.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {K : Type*} [Field K] {n : ℕ}

/-- The rescaling of power series sends a variable to its multiple. -/
theorem rescaleAlgHom_X_eq {σ : Type*} (a : σ → K) (i : σ) :
    rescaleAlgHom a (X i : MvPowerSeries σ K) = C (a i) * X i := by
  classical
  rw [rescaleAlgHom_apply]
  ext d
  rw [coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with h
  · subst h
    simp [Finsupp.prod_single_index]
  · simp

/-- A K-algebra map of power series fixes the constants. -/
theorem algHom_C {σ τ : Type*} (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries τ K) (c : K) :
    ψ (C c) = C c := by
  rw [show (C c : MvPowerSeries σ K) = algebraMap K (MvPowerSeries σ K) c from rfl,
    AlgHom.commutes]
  rfl

/-- The scalar of a diagonal transform of a monomial in the chart x_k = 1. -/
theorem diagonal_chart_scalar (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (k : Fin n)
    (q : Fin n →₀ ℕ) :
    (t ^ w k) ^ (∑ i, q i) * ∏ i : {i : Fin n // i ≠ k}, (t ^ w i / t ^ w k) ^ (q i) =
      t ^ polynomialExponentWeight w q := by
  classical
  have htk : t ^ w k ≠ 0 := pow_ne_zero _ ht
  have hsum : ∑ i, q i = q k + ∑ i : {i : Fin n // i ≠ k}, q i := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k),
      Finset.sum_subtype (p := fun i => i ≠ k) (Finset.univ.erase k) (fun i => by simp)]
  have hweight : polynomialExponentWeight w q =
      w k * q k + ∑ i : {i : Fin n // i ≠ k}, w i * q i := by
    unfold polynomialExponentWeight
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k),
      Finset.sum_subtype (p := fun i => i ≠ k) (Finset.univ.erase k) (fun i => by simp)]
  have hprod : ∏ i : {i : Fin n // i ≠ k}, (t ^ w i / t ^ w k) ^ (q i) =
      t ^ (∑ i : {i : Fin n // i ≠ k}, w i * q i) /
        (t ^ w k) ^ (∑ i : {i : Fin n // i ≠ k}, q i) := by
    simp only [div_pow, Finset.prod_div_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    rw [Finset.mul_sum]
  rw [hsum, hweight, hprod, pow_add, pow_add, ← pow_mul]
  field_simp

/-- The rescaling of a product of shifted coordinates. -/
theorem rescaleAlgHom_shifted_prod {σ : Type*} [Fintype σ] (μ p : σ → K) (q : σ → ℕ) :
    rescaleAlgHom μ (∏ i, (C (μ i * p i) + X i) ^ (q i)) =
      C (∏ i, μ i ^ (q i)) * ∏ i, (C (p i) + X i) ^ (q i) := by
  rw [map_prod]
  have hf : ∀ i, rescaleAlgHom μ ((C (μ i * p i) + X i) ^ (q i)) =
      C (μ i ^ (q i)) * (C (p i) + X i) ^ (q i) := by
    intro i
    rw [map_pow, map_add, algHom_C, rescaleAlgHom_X_eq,
      show (C (μ i * p i) : MvPowerSeries σ K) = C (μ i) * C (p i) from map_mul _ _ _,
      ← mul_add, mul_pow, ← map_pow]
  simp only [hf, Finset.prod_mul_distrib, ← map_prod]

/-- The diagonal transform of a monomial in the chart x_k = 1. -/
theorem chartShiftedForm_polynomialDiagonalHom_monomial (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) (p : {i : Fin n // i ≠ k} → K) (q : Fin n →₀ ℕ) (c : K) :
    chartShiftedForm k p (polynomialDiagonalHom w t (MvPolynomial.monomial q c)) =
      C ((t ^ w k) ^ (∑ i, q i)) *
        rescaleAlgHom (fun i : {i : Fin n // i ≠ k} => t ^ w i / t ^ w k)
          (chartShiftedForm k (fun i => t ^ w i / t ^ w k * p i) (MvPolynomial.monomial q c)) := by
  classical
  rw [polynomialDiagonalHom_monomial, MvPolynomial.C_mul_monomial, chartShiftedForm_monomial,
    chartShiftedForm_monomial]
  have hres : rescaleAlgHom (fun i : {i : Fin n // i ≠ k} => t ^ w i / t ^ w k)
      (C c * ∏ i : {i : Fin n // i ≠ k}, (C (t ^ w i.val / t ^ w k * p i) + X i) ^ (q i)) =
      C c * (C (∏ i : {i : Fin n // i ≠ k}, (t ^ w i.val / t ^ w k) ^ (q i)) *
        ∏ i : {i : Fin n // i ≠ k}, (C (p i) + X i) ^ (q i)) := by
    rw [map_mul, algHom_C, rescaleAlgHom_shifted_prod (fun i : {i : Fin n // i ≠ k} =>
      t ^ w i.val / t ^ w k) p (fun i => q i)]
  rw [hres, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
  congr 2
  rw [← diagonal_chart_scalar w ht k q]
  ring

/-- The diagonal transform of a form of degree D in the chart x_k = 1. -/
theorem chartShiftedForm_polynomialDiagonalHom (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (k : Fin n) (p : {i : Fin n // i ≠ k} → K) {g : MvPolynomial (Fin n) K} {D : ℕ}
    (hg : g.IsHomogeneous D) :
    chartShiftedForm k p (polynomialDiagonalHom w t g) =
      C ((t ^ w k) ^ D) *
        rescaleAlgHom (fun i : {i : Fin n // i ≠ k} => t ^ w i / t ^ w k)
          (chartShiftedForm k (fun i => t ^ w i / t ^ w k * p i) g) := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum g]
  conv_rhs => rw [MvPolynomial.as_sum g]
  unfold chartShiftedForm
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hdeg : ∑ i, q i = D := by
    have h := hg (MvPolynomial.mem_support_iff.mp hq)
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have h := chartShiftedForm_polynomialDiagonalHom_monomial w ht k p q (g.coeff q)
  unfold chartShiftedForm at h
  rw [h, hdeg]

/-- The Jacobian determinant of a test valuation composed with a rescaling. -/
theorem powerSeriesJacobian_det_comp_rescale {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (a : σ → K) :
    (powerSeriesJacobian (ψ.comp (rescaleAlgHom a))).det =
      C (∏ i, a i) * (powerSeriesJacobian ψ).det := by
  have hJ : powerSeriesJacobian (ψ.comp (rescaleAlgHom a)) =
      Matrix.of fun i j => C (a i) * powerSeriesJacobian ψ i j := by
    ext i j
    simp only [powerSeriesJacobian, Matrix.of_apply, AlgHom.comp_apply, rescaleAlgHom_X_eq,
      map_mul, algHom_C]
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  rw [hJ, Matrix.det_mul_column, map_prod]

/-- The threshold condition (34) passes to the diagonal transforms of the forms. -/
theorem projectiveThresholdCondition_polynomialDiagonalHom [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (hg : ∀ ℓ, ∃ D, (g ℓ).IsHomogeneous D)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (h : ℕ) (hcond : ProjectiveThresholdCondition g h) :
    ProjectiveThresholdCondition (fun ℓ => polynomialDiagonalHom w t (g ℓ)) h := by
  intro k p ψ hψ hdet wt hwt
  set μ : {i : Fin n // i ≠ k} → K := fun i => t ^ w i / t ^ w k with hμdef
  have hμ : ∀ i, μ i ≠ 0 := fun i => div_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ ht)
  have hψ' : ∀ i, (ψ.comp (rescaleAlgHom μ)) (X i) ≠ 0 := by
    intro i
    rw [AlgHom.comp_apply, rescaleAlgHom_X_eq, map_mul, algHom_C]
    exact mul_ne_zero ((isUnit_iff_ne_zero.mpr (hμ i)).map (C (σ := {i : Fin n // i ≠ k}))).ne_zero
      (hψ i)
  have hdet' : (powerSeriesJacobian (ψ.comp (rescaleAlgHom μ))).det ≠ 0 := by
    rw [powerSeriesJacobian_det_comp_rescale]
    exact mul_ne_zero ((isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hμ i)).map
      (C (σ := {i : Fin n // i ≠ k}))).ne_zero hdet
  obtain ⟨ℓ, hℓ⟩ := hcond k (fun i => μ i * p i) (ψ.comp (rescaleAlgHom μ)) hψ' hdet' wt hwt
  refine ⟨ℓ, ?_⟩
  obtain ⟨D, hD⟩ := hg ℓ
  have hunit : ∀ c : K, c ≠ 0 →
      (C c : MvPowerSeries {i : Fin n // i ≠ k} K).weightedOrder wt = 0 := fun c hc =>
    weightedOrder_eq_zero_of_isUnit wt ((isUnit_iff_ne_zero.mpr hc).map _)
  simp only
  rw [chartShiftedForm_polynomialDiagonalHom w ht k p hD, map_mul, algHom_C, weightedOrder_mul,
    hunit _ (pow_ne_zero _ (pow_ne_zero _ ht)), zero_add]
  rw [powerSeriesJacobian_det_comp_rescale, weightedOrder_mul,
    hunit _ (Finset.prod_ne_zero_iff.mpr fun i _ => hμ i), zero_add] at hℓ
  exact hℓ

/-- The diagonal transform by t⁻¹ undoes the one by t. -/
theorem polynomialDiagonalHom_inv_apply (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (f : MvPolynomial (Fin n) K) :
    polynomialDiagonalHom w t⁻¹ (polynomialDiagonalHom w t f) = f := by
  have hcomp : (polynomialDiagonalHom w t⁻¹).comp (polynomialDiagonalHom w t) =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDiagonalHom]
    · intro i
      simp only [polynomialDiagonalHom, RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
        map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      rw [← mul_assoc, ← map_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ ht), map_one, one_mul]
  exact congrArg (fun φ => φ f) hcomp

/-- The threshold condition (34) for the diagonal transforms of the forms by t ≠ 0 gives the
condition for the forms. -/
theorem projectiveThresholdCondition_of_polynomialDiagonalHom [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (hg : ∀ ℓ, ∃ D, (g ℓ).IsHomogeneous D)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (h : ℕ)
    (hcond : ProjectiveThresholdCondition (fun ℓ => polynomialDiagonalHom w t (g ℓ)) h) :
    ProjectiveThresholdCondition g h := by
  have h' := projectiveThresholdCondition_polynomialDiagonalHom
    (fun ℓ => polynomialDiagonalHom w t (g ℓ))
    (fun ℓ => (hg ℓ).imp fun D hD => polynomialDiagonalHom_isHomogeneous w t hD) w
    (inv_ne_zero ht) h hcond
  simpa only [polynomialDiagonalHom_inv_apply w ht] using h'

/-- Nonzero constant multiples of the forms satisfy the threshold condition (34) exactly when the
forms do. -/
theorem projectiveThresholdCondition_C_mul_iff [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (c : ι → K) (hc : ∀ ℓ, c ℓ ≠ 0) (h : ℕ) :
    ProjectiveThresholdCondition (fun ℓ => MvPolynomial.C (c ℓ) * g ℓ) h ↔
      ProjectiveThresholdCondition g h := by
  have hform : ∀ k p ℓ, chartShiftedForm k p (MvPolynomial.C (c ℓ) * g ℓ) =
      C (c ℓ) * chartShiftedForm k p (g ℓ) := by
    intro k p ℓ
    unfold chartShiftedForm
    rw [map_mul, MvPolynomial.aeval_C]
    rfl
  have hval : ∀ (k : Fin n) (ψ : MvPowerSeries {i : Fin n // i ≠ k} K →ₐ[K]
      MvPowerSeries {i : Fin n // i ≠ k} K) (wt : {i : Fin n // i ≠ k} → ℕ) p ℓ,
      (ψ (chartShiftedForm k p (MvPolynomial.C (c ℓ) * g ℓ))).weightedOrder wt =
        (ψ (chartShiftedForm k p (g ℓ))).weightedOrder wt := by
    intro k ψ wt p ℓ
    rw [hform, map_mul, algHom_C, weightedOrder_mul,
      weightedOrder_eq_zero_of_isUnit wt ((isUnit_iff_ne_zero.mpr (hc ℓ)).map _), zero_add]
  constructor
  · intro hcond k p ψ hψ hdet wt hwt
    obtain ⟨ℓ, hℓ⟩ := hcond k p ψ hψ hdet wt hwt
    exact ⟨ℓ, by rwa [hval] at hℓ⟩
  · intro hcond k p ψ hψ hdet wt hwt
    obtain ⟨ℓ, hℓ⟩ := hcond k p ψ hψ hdet wt hwt
    exact ⟨ℓ, by rwa [hval]⟩

end MixedFujita
