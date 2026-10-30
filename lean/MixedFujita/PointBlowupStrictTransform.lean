/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricExtraction

/-!
The strict transform under the blow-up of a point, in the chart where u_k generates (§8). The
chart x_k = u_k, x_i = u_i u_k sends x^e to u^(e♯), where e♯ has k-th entry |e| and the other
entries of e; conversely d is such an image exactly when Σ_{i≠k} d_i ≤ d_k. A series f whose
monomials all have degree at least m is u_k^m times its strict transform g, and the part of g
free of u_k is the leading form f_m dehomogenized at x_k = 1: the coefficient of g at u^d with
d_k = 0 is the coefficient of f at d + (m - Σ_{i≠k} d_i) e_k. Hence on the exceptional divisor
E = {u_k = 0} the strict transforms of sections of multiplicity m restrict to their leading forms
of degree m, the generators of 𝔟|_E in (34), and E is not a component of the strict transform when
the leading form is nonzero.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The chart of the blow-up of the origin in which u_k generates. -/
@[reducible]
def pointBlowupChart (k : σ) : Matrix σ σ ℕ := blowupChartMatrix Finset.univ k

theorem pointBlowupChart_row_ne_zero (k : σ) (i : σ) : ∃ j, pointBlowupChart k i j ≠ 0 := by
  refine ⟨i, ?_⟩
  simp [pointBlowupChart, blowupChartMatrix]

theorem monomialImageExponent_pointBlowupChart_injective (k : σ) :
    Function.Injective (monomialImageExponent (pointBlowupChart k)) := by
  intro e e' h
  have h' := congrArg (fun x : σ →₀ ℕ => (x : σ → ℕ)) h
  simp only [monomialImageExponent, Finsupp.coe_equivFunOnFinite_symm] at h'
  exact DFunLike.coe_injective (vecMul_blowupChartMatrix_injective Finset.univ k h')

/-- The image exponent: the k-th entry becomes the degree, the others are kept. -/
theorem monomialImageExponent_pointBlowupChart_apply (k : σ) (e : σ →₀ ℕ) (l : σ) :
    monomialImageExponent (pointBlowupChart k) e l = if l = k then e.degree else e l := by
  simp only [monomialImageExponent, Finsupp.coe_equivFunOnFinite_symm]
  by_cases hl : l = k
  · subst hl
    rw [vecMul_blowupChartMatrix_self, ite_eq_left rfl, Finsupp.degree_eq_sum]
    have h : (∑ i, if i ∈ Finset.univ ∧ i ≠ l then e i else 0) =
        ∑ i ∈ Finset.univ.erase l, e i := by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    rw [h, Finset.add_sum_erase _ _ (Finset.mem_univ l)]
  · rw [vecMul_blowupChartMatrix_of_ne _ hl, ite_eq_right hl]

/-- The candidate preimage of an exponent d: the k-th entry becomes d_k - Σ_{i≠k} d_i. -/
noncomputable def pointBlowupPreimage (k : σ) (d : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => if l = k then d k - ∑ i ∈ Finset.univ.erase k, d i else d l

theorem pointBlowupPreimage_apply (k : σ) (d : σ →₀ ℕ) (l : σ) :
    pointBlowupPreimage k d l = if l = k then d k - ∑ i ∈ Finset.univ.erase k, d i else d l :=
  rfl

theorem monomialImageExponent_pointBlowupPreimage (k : σ) (d : σ →₀ ℕ)
    (hd : ∑ i ∈ Finset.univ.erase k, d i ≤ d k) :
    monomialImageExponent (pointBlowupChart k) (pointBlowupPreimage k d) = d := by
  ext l
  rw [monomialImageExponent_pointBlowupChart_apply]
  by_cases hl : l = k
  · subst hl
    rw [ite_eq_left rfl, Finsupp.degree_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    have hrest : ∑ i ∈ Finset.univ.erase l, pointBlowupPreimage l d i =
        ∑ i ∈ Finset.univ.erase l, d i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [pointBlowupPreimage, (Finset.mem_erase.mp hi).1]
    rw [hrest]
    simp only [pointBlowupPreimage, Finsupp.coe_equivFunOnFinite_symm, ite_true]
    omega
  · rw [ite_eq_right hl]
    simp [pointBlowupPreimage, hl]

theorem sum_erase_le_of_eq_monomialImageExponent (k : σ) (e : σ →₀ ℕ) :
    ∑ i ∈ Finset.univ.erase k, monomialImageExponent (pointBlowupChart k) e i ≤
      monomialImageExponent (pointBlowupChart k) e k := by
  rw [monomialImageExponent_pointBlowupChart_apply, ite_eq_left rfl, Finsupp.degree_eq_sum,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have h : ∑ i ∈ Finset.univ.erase k, monomialImageExponent (pointBlowupChart k) e i =
      ∑ i ∈ Finset.univ.erase k, e i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [monomialImageExponent_pointBlowupChart_apply, ite_eq_right (Finset.mem_erase.mp hi).1]
  rw [h]
  omega

/-- The coefficients of the pulled-back series. -/
theorem coeff_subst_pointBlowup (k : σ) (f : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    coeff d (subst (monomialSubstVars (K := K) (pointBlowupChart k)) f) =
      if ∑ i ∈ Finset.univ.erase k, d i ≤ d k then coeff (pointBlowupPreimage k d) f else 0 := by
  by_cases hd : ∑ i ∈ Finset.univ.erase k, d i ≤ d k
  · rw [ite_eq_left hd]
    conv_lhs => rw [← monomialImageExponent_pointBlowupPreimage k d hd]
    exact coeff_subst_monomialSubstVars (pointBlowupChart_row_ne_zero k)
      (monomialImageExponent_pointBlowupChart_injective k) f _
  · rw [ite_eq_right hd]
    apply coeff_subst_monomialSubstVars_of_notMem (pointBlowupChart_row_ne_zero k)
    intro e he
    apply hd
    rw [← he]
    exact sum_erase_le_of_eq_monomialImageExponent k e

/-- The strict transform g with Φ f = u_k^m · g. -/
noncomputable def pointBlowupStrictTransform (k : σ) (m : ℕ) (f : MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  fun d => coeff (d + Finsupp.single k m) (subst (monomialSubstVars (K := K) (pointBlowupChart k)) f)

theorem coeff_pointBlowupStrictTransform (k : σ) (m : ℕ) (f : MvPowerSeries σ K)
    (d : σ →₀ ℕ) :
    coeff d (pointBlowupStrictTransform k m f) =
      coeff (d + Finsupp.single k m) (subst (monomialSubstVars (K := K) (pointBlowupChart k)) f) :=
  rfl

/-- A series of order at least m pulls back to u_k^m times its strict transform. -/
theorem subst_pointBlowup_eq_mul (k : σ) (m : ℕ) (f : MvPowerSeries σ K)
    (hf : (m : ℕ∞) ≤ f.order) :
    subst (monomialSubstVars (K := K) (pointBlowupChart k)) f =
      monomial (Finsupp.single k m) 1 * pointBlowupStrictTransform k m f := by
  ext d
  rw [coeff_monomial_mul]
  by_cases hdk : Finsupp.single k m ≤ d
  · rw [ite_eq_left hdk, one_mul, coeff_pointBlowupStrictTransform, tsub_add_cancel_of_le hdk]
  · rw [ite_eq_right hdk, coeff_subst_pointBlowup]
    have hdk' : d k < m := by
      by_contra h
      push Not at h
      apply hdk
      intro l
      rw [Finsupp.single_apply]
      split_ifs with hl
      · subst hl
        exact h
      · exact Nat.zero_le _
    by_cases hd : ∑ i ∈ Finset.univ.erase k, d i ≤ d k
    · rw [ite_eq_left hd]
      apply coeff_of_lt_order
      -- the preimage has degree d k < m ≤ ord f
      have hdeg : (pointBlowupPreimage k d).degree = d k := by
        have h := monomialImageExponent_pointBlowupChart_apply k (pointBlowupPreimage k d) k
        rw [monomialImageExponent_pointBlowupPreimage k d hd, ite_eq_left rfl] at h
        exact h.symm
      rw [hdeg]
      exact lt_of_lt_of_le (by exact_mod_cast hdk') hf
    · rw [ite_eq_right hd]

/-- On E = {u_k = 0} the strict transform is the leading form dehomogenized at x_k = 1. -/
theorem coeff_pointBlowupStrictTransform_of_eq_zero (k : σ) (m : ℕ) (f : MvPowerSeries σ K)
    (d : σ →₀ ℕ) (hd : d k = 0) :
    coeff d (pointBlowupStrictTransform k m f) =
      if ∑ i ∈ Finset.univ.erase k, d i ≤ m then
        coeff (d + Finsupp.single k (m - ∑ i ∈ Finset.univ.erase k, d i)) f else 0 := by
  rw [coeff_pointBlowupStrictTransform, coeff_subst_pointBlowup]
  have hk : (d + Finsupp.single k m) k = m := by simp [hd]
  have hrest : ∑ i ∈ Finset.univ.erase k, (d + Finsupp.single k m) i =
      ∑ i ∈ Finset.univ.erase k, d i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [Ne.symm (Finset.mem_erase.mp hi).1]
  rw [hk, hrest]
  by_cases hle : ∑ i ∈ Finset.univ.erase k, d i ≤ m
  · rw [ite_eq_left hle, ite_eq_left hle]
    have hexp : pointBlowupPreimage k (d + Finsupp.single k m) =
        d + Finsupp.single k (m - ∑ i ∈ Finset.univ.erase k, d i) := by
      ext l
      rw [pointBlowupPreimage_apply]
      by_cases hl : l = k
      · subst hl
        rw [ite_eq_left rfl, hk, hrest, Finsupp.add_apply, hd, Finsupp.single_eq_same, zero_add]
      · rw [ite_eq_right hl]
        simp [Ne.symm hl]
    rw [hexp]
  · rw [ite_eq_right hle, ite_eq_right hle]

/-- E is not a component of the strict transform when the leading form of degree m is nonzero. -/
theorem exists_coeff_pointBlowupStrictTransform_ne_zero (k : σ) (m : ℕ) (f : MvPowerSeries σ K)
    {e : σ →₀ ℕ} (he : e.degree = m) (hfe : coeff e f ≠ 0) :
    ∃ d : σ →₀ ℕ, d k = 0 ∧ coeff d (pointBlowupStrictTransform k m f) ≠ 0 := by
  set d : σ →₀ ℕ := e - Finsupp.single k (e k) with hd
  have hdk : d k = 0 := by simp [hd]
  have hrest : ∑ i ∈ Finset.univ.erase k, d i = ∑ i ∈ Finset.univ.erase k, e i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [hd, Ne.symm (Finset.mem_erase.mp hi).1]
  have hsum : e k + ∑ i ∈ Finset.univ.erase k, e i = m := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ k), ← Finsupp.degree_eq_sum, he]
  refine ⟨d, hdk, ?_⟩
  rw [coeff_pointBlowupStrictTransform_of_eq_zero k m f d hdk, hrest,
    ite_eq_left (by omega)]
  have hexp : d + Finsupp.single k (m - ∑ i ∈ Finset.univ.erase k, e i) = e := by
    ext l
    by_cases hl : l = k
    · subst hl
      simp only [hd, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [hd, Ne.symm hl]
  rw [hexp]
  exact hfe

end MixedFujita
