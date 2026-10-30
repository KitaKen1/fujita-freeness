/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.UniversalParameterFieldFibers

/-!
Fix one coefficient vector before varying T. This is a single homogeneous
form over K[T], obtained by an actual coefficient-ring map from the universal
form. At nonzero T, inverse powers of T correct the coefficients so that the
fiber is the diagonal transform of a linear combination of the original
generators. Nonzero special fiber implies a nonzero global equation, not
nonvanishing at every parameter. No Bertini or threshold theorem is assumed.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {K ι : Type u} [Field K]

noncomputable def fixedCoefficientParameterForm
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) :
    MvPolynomial (Fin n) (Polynomial K) :=
  ∑ l ∈ I, MvPolynomial.C (Polynomial.C (a l)) * homogeneousParameterFamily w (p l) (f l)

theorem fixedCoefficientParameterForm_from_universal
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) :
    fixedCoefficientParameterForm I w p f a =
      MvPolynomial.map (MvPolynomial.eval₂Hom (RingHom.id (Polynomial K))
        (fun l => Polynomial.C (a l))) (universalParameterHomogeneousForm I w p f) :=
  (universalHomogeneousForm_specialize I _ _).symm

theorem fixedCoefficientParameterForm_isHomogeneous
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (fixedCoefficientParameterForm I w p f a).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro l hl
  exact (homogeneousParameterFamily_isHomogeneous w (p l) (hf l hl)).C_mul _

theorem fixedCoefficientParameterForm_eval
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (t : K) :
    MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a) =
      ∑ l ∈ I, MvPolynomial.C (a l) *
        (weightedPolynomialFamily w (p l) (f l)).eval (MvPolynomial.C t) := by
  classical
  simp only [fixedCoefficientParameterForm, map_sum, map_mul, MvPolynomial.map_C,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, homogeneousParameterFamily_baseChange]

theorem fixedCoefficientParameterForm_eval_universal
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (t : K) :
    MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a) =
      MvPolynomial.map (universalParameterCoefficientEval t a)
        (universalParameterHomogeneousForm I w p f) := by
  rw [fixedCoefficientParameterForm_eval, universalParameterCoefficientEval_form]

theorem fixedCoefficientParameterForm_at_zero
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (fixedCoefficientParameterForm I w p f a) =
      ∑ l ∈ I, MvPolynomial.C (a l) * MvPolynomial.monomial (p l) ((f l).coeff (p l)) := by
  rw [fixedCoefficientParameterForm_eval_universal,
    universalParameterCoefficientEval_at_zero I w p f hp hw a]

theorem fixedCoefficientParameterForm_at_one
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) :
    MvPolynomial.map (Polynomial.evalRingHom 1) (fixedCoefficientParameterForm I w p f a) =
      ∑ l ∈ I, MvPolynomial.C (a l) * f l := by
  rw [fixedCoefficientParameterForm_eval_universal, universalParameterCoefficientEval_at_one]

theorem fixedCoefficientParameterForm_ne_zero_of_fiber
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (t : K)
    (h : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p f a) ≠ 0) :
    fixedCoefficientParameterForm I w p f a ≠ 0 := by
  intro h0
  exact h (by rw [h0, map_zero])

theorem weightedPolynomialFamily_unscaled_parameter
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) {t : K}
    (ht : t ≠ 0)
    (hw : ∀ q ∈ f.support, polynomialExponentWeight w p ≤ polynomialExponentWeight w q) :
    (weightedPolynomialFamily w p f).eval (MvPolynomial.C t) =
      MvPolynomial.C ((t ^ polynomialExponentWeight w p)⁻¹) * polynomialDiagonalHom w t f := by
  rw [← weightedPolynomialFamily_scaled_parameter w p f t hw, ← mul_assoc,
    ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ ht), map_one, one_mul]

noncomputable def correctedCoefficientVector
    (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ) (a : ι → K) (t : K) : ι → K :=
  fun l => a l * (t ^ polynomialExponentWeight w (p l))⁻¹

theorem fixedCoefficientParameterForm_nonzero_parameter_diagonal
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a) =
      polynomialDiagonalHom w t
        (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) := by
  classical
  rw [fixedCoefficientParameterForm_eval]
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro l hl
  rw [weightedPolynomialFamily_unscaled_parameter w (p l) (f l) ht (hw l hl),
    ← mul_assoc, ← MvPolynomial.C_mul]
  congr 1
  simp [polynomialDiagonalHom, correctedCoefficientVector]

theorem polynomialLinearCombination_mem_span
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (a : ι → K) :
    ∑ l ∈ I, MvPolynomial.C (a l) * f l ∈
      Ideal.span (Set.range (fun l : I => f l)) := by
  classical
  apply Ideal.sum_mem
  intro l hl
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨l, hl⟩, rfl⟩)

theorem fixedCoefficientParameterForm_nonzero_original_combination
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (h0 : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p f a) ≠ 0) :
    (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) ≠ 0 ∧
      (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) ∈
        Ideal.span (Set.range (fun l : I => f l)) := by
  refine ⟨?_, polynomialLinearCombination_mem_span I f _⟩
  intro h
  apply h0
  rw [fixedCoefficientParameterForm_nonzero_parameter_diagonal I w p f a ht hw,
    h, map_zero]

end MixedFujita
