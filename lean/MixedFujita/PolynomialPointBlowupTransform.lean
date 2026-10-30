/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupExceptionalSeries
public import Hironaka.Scheme.BlowUp.Model

/-!
The polynomial point-blow-up substitution and the actual polynomial strict transform. Its
coercion is exactly the existing formal strict transform whenever the polynomial has order
at least m. These are finite polynomial formulas, so later exceptional-chart translations
at arbitrary points are legitimate polynomial evaluations.
-/

@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {K : Type*} [Field K]

noncomputable def polynomialPointBlowupMap (k : Fin n) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  AlgebraicGeometry.affineBlowUpAlgebra.chartSubst K Set.univ k

theorem polynomialPointBlowupMap_X_self (k : Fin n) :
    polynomialPointBlowupMap (K := K) k (MvPolynomial.X k) = MvPolynomial.X k :=
  AlgebraicGeometry.affineBlowUpAlgebra.chartSubst_X_self K Set.univ k

theorem polynomialPointBlowupMap_X_other (k i : Fin n) (hi : i ≠ k) :
    polynomialPointBlowupMap (K := K) k (MvPolynomial.X i) = MvPolynomial.X i * MvPolynomial.X k :=
  AlgebraicGeometry.affineBlowUpAlgebra.chartSubst_X_of_mem K Set.univ k (Set.mem_univ i) hi

theorem monomialSubstVars_pointBlowupChart (k i : Fin n) :
    monomialSubstVars (K := K) (pointBlowupChart k) i =
      if i = k then MvPowerSeries.X k else MvPowerSeries.X i * MvPowerSeries.X k := by
  classical
  have he : matrixRowExponent (pointBlowupChart k) i =
      if i = k then Finsupp.single k 1 else Finsupp.single i 1 + Finsupp.single k 1 := by
    ext j
    by_cases hi : i = k
    · subst i
      simp [matrixRowExponent, pointBlowupChart, blowupChartMatrix, Matrix.one_apply,
        Finsupp.single_apply]
    · by_cases hj : j = k
      · subst j
        simp [matrixRowExponent, pointBlowupChart, blowupChartMatrix, hi, Ne.symm hi]
      · simp [matrixRowExponent, pointBlowupChart, blowupChartMatrix, Matrix.one_apply,
          Finsupp.single_apply, hi, hj]
  rw [monomialSubstVars, he]
  split_ifs with hi
  · rfl
  · rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]

theorem polynomialPointBlowupMap_coe (k : Fin n) (f : MvPolynomial (Fin n) K) :
    (polynomialPointBlowupMap k f : MvPowerSeries (Fin n) K) =
      MvPowerSeries.subst (monomialSubstVars (K := K) (pointBlowupChart k))
        (f : MvPowerSeries (Fin n) K) := by
  have hsubst := hasSubst_monomialSubstVars (K := K) (pointBlowupChart_row_ne_zero k)
  have hX (i : Fin n) :
      (polynomialPointBlowupMap (K := K) k (MvPolynomial.X i) : MvPowerSeries (Fin n) K) =
        monomialSubstVars (K := K) (pointBlowupChart k) i := by
    rw [monomialSubstVars_pointBlowupChart]
    by_cases hi : i = k
    · subst i
      rw [polynomialPointBlowupMap_X_self, ite_eq_left rfl, MvPolynomial.coe_X]
    · rw [polynomialPointBlowupMap_X_other k i hi, ite_eq_right hi, MvPolynomial.coe_mul,
        MvPolynomial.coe_X, MvPolynomial.coe_X]
  induction f using MvPolynomial.induction_on with
  | C r => simp [polynomialPointBlowupMap]
  | add f g hf hg =>
    rw [map_add, MvPolynomial.coe_add, MvPolynomial.coe_add, MvPowerSeries.subst_add hsubst, hf, hg]
  | mul_X f i hf =>
    rw [map_mul, MvPolynomial.coe_mul, MvPolynomial.coe_mul, MvPowerSeries.subst_mul hsubst,
      MvPolynomial.coe_X, MvPowerSeries.subst_X hsubst, hf, hX]

theorem polynomialPointBlowupMap_monomial (k : Fin n) (p : Fin n →₀ ℕ) (r : K) :
    polynomialPointBlowupMap k (MvPolynomial.monomial p r) =
      MvPolynomial.monomial (monomialImageExponent (pointBlowupChart k) p) r := by
  apply MvPolynomial.coe_injective (Fin n) K
  rw [polynomialPointBlowupMap_coe, MvPolynomial.coe_monomial, MvPolynomial.coe_monomial,
    MvPowerSeries.subst_monomial (hasSubst_monomialSubstVars (pointBlowupChart_row_ne_zero k)),
    prod_monomialSubstVars]
  change MvPowerSeries.C r * MvPowerSeries.monomial _ 1 = MvPowerSeries.monomial _ r
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial,
    zero_add, mul_one]

noncomputable def polynomialPointBlowupStrictTransform (k : Fin n) (m : ℕ)
    (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  ∑ p ∈ f.support, if m ≤ p.degree then MvPolynomial.monomial
    (monomialImageExponent (pointBlowupChart k) p - Finsupp.single k m) (f.coeff p) else 0

theorem polynomialPointBlowupMap_factor (k : Fin n) (m : ℕ) (f : MvPolynomial (Fin n) K)
    (hf : (m : ℕ∞) ≤ (f : MvPowerSeries (Fin n) K).order) :
    polynomialPointBlowupMap k f =
      MvPolynomial.X k ^ m * polynomialPointBlowupStrictTransform k m f := by
  classical
  have hdeg (p : Fin n →₀ ℕ) (hp : p ∈ f.support) : m ≤ p.degree := by
    have hne : MvPowerSeries.coeff p (f : MvPowerSeries (Fin n) K) ≠ 0 := by
      simpa only [MvPolynomial.coeff_coe] using MvPolynomial.mem_support_iff.mp hp
    exact_mod_cast hf.trans (MvPowerSeries.order_le hne)
  conv_lhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, polynomialPointBlowupStrictTransform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [polynomialPointBlowupMap_monomial, ite_eq_left (hdeg p hp)]
  have hle : Finsupp.single k m ≤ monomialImageExponent (pointBlowupChart k) p := by
    intro i
    rw [monomialImageExponent_pointBlowupChart_apply, Finsupp.single_apply]
    by_cases hi : i = k
    · simp only [hi, ite_true]
      exact hdeg p hp
    · simp only [hi, Ne.symm hi, ite_false]
      exact Nat.zero_le _
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    one_mul, add_tsub_cancel_of_le hle]

theorem polynomialPointBlowupStrictTransform_coe (k : Fin n) (m : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : (m : ℕ∞) ≤ (f : MvPowerSeries (Fin n) K).order) :
    (polynomialPointBlowupStrictTransform k m f : MvPowerSeries (Fin n) K) =
      pointBlowupStrictTransform k m f := by
  have hpoly := congrArg (fun q : MvPolynomial (Fin n) K => (q : MvPowerSeries (Fin n) K))
    (polynomialPointBlowupMap_factor k m f hf)
  rw [polynomialPointBlowupMap_coe, MvPolynomial.coe_mul, MvPolynomial.coe_pow,
    MvPolynomial.coe_X, MvPowerSeries.X_pow_eq] at hpoly
  have hformal := subst_pointBlowup_eq_mul k m (f : MvPowerSeries (Fin n) K) hf
  apply MvPowerSeries.ext
  intro p
  have he := congrArg (MvPowerSeries.coeff (Finsupp.single k m + p))
    (hpoly.symm.trans hformal)
  simpa only [MvPowerSeries.coeff_monomial_mul, le_self_add, ite_eq_left,
    add_tsub_cancel_left, one_mul] using he

end MixedFujita
