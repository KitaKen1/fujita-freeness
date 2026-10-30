/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HomogeneousTaylor
public import MixedFujita.TauDegreeNormalization

/-!
The diagonal family as actual homogeneous polynomials over K[T]. Scalar
base change agrees with the previously constructed polynomial family.
Degree-lex initial power series of one degree provide the homogeneous
inputs. This constructs algebraic graded data, not a projective Scheme
family or a log canonical threshold theorem.
-/

@[expose] public section

namespace MixedFujita

variable {n : ℕ} {K : Type*} [Field K]

noncomputable def homogeneousParameterFamily (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    (f : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) (Polynomial K) :=
  ∑ q ∈ f.support, MvPolynomial.monomial q
    (Polynomial.monomial
      (polynomialExponentWeight w q - polynomialExponentWeight w p) (f.coeff q))

theorem homogeneousParameterFamily_isHomogeneous (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (homogeneousParameterFamily w p f).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro q hq
  apply MvPolynomial.isHomogeneous_monomial
  have hd := hf (MvPolynomial.mem_support_iff.mp hq)
  simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using hd

theorem homogeneousParameterFamily_baseChange (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    (f : MvPolynomial (Fin n) K) (t : K) :
    MvPolynomial.map (Polynomial.evalRingHom t) (homogeneousParameterFamily w p f) =
      (weightedPolynomialFamily w p f).eval (MvPolynomial.C t) := by
  classical
  simp only [homogeneousParameterFamily, weightedPolynomialFamily, map_sum,
    MvPolynomial.map_monomial, Polynomial.coe_evalRingHom, Polynomial.eval_monomial,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro q _
  rw [← map_pow, mul_comm (MvPolynomial.monomial q (f.coeff q)),
    MvPolynomial.C_mul_monomial]
  congr 1
  exact mul_comm _ _

theorem homogeneousParameterFamily_at_one (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    (f : MvPolynomial (Fin n) K) :
    MvPolynomial.map (Polynomial.evalRingHom 1) (homogeneousParameterFamily w p f) = f := by
  rw [homogeneousParameterFamily_baseChange, map_one, weightedPolynomialFamily_at_one]

theorem homogeneousParameterFamily_at_zero (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    (f : MvPolynomial (Fin n) K) (hp : p ∈ f.support)
    (hw : ∀ q ∈ f.support, q ≠ p →
      polynomialExponentWeight w p < polynomialExponentWeight w q) :
    MvPolynomial.map (Polynomial.evalRingHom 0) (homogeneousParameterFamily w p f) =
      MvPolynomial.monomial p (f.coeff p) := by
  rw [homogeneousParameterFamily_baseChange, map_zero,
    weightedPolynomialFamily_at_zero w p f hp hw]

theorem homogeneousParameterFamily_nonzero (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    {f : MvPolynomial (Fin n) K} (hf : f ≠ 0) : homogeneousParameterFamily w p f ≠ 0 := by
  intro h
  apply hf
  have h' := homogeneousParameterFamily_at_one w p f
  rw [h, map_zero] at h'
  exact h'.symm

theorem homogeneousParameterFamily_totalDegree (w : Fin n → ℕ) (p : Fin n →₀ ℕ)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    (homogeneousParameterFamily w p f).totalDegree = d :=
  (homogeneousParameterFamily_isHomogeneous w p hf).totalDegree
    (homogeneousParameterFamily_nonzero w p hf0)

theorem polynomialDiagonalHom_isHomogeneous (w : Fin n → ℕ) (t : K)
    {f : MvPolynomial (Fin n) K} {d : ℕ} (hf : f.IsHomogeneous d) :
    (polynomialDiagonalHom w t f).IsHomogeneous d := by
  simpa only [polynomialDiagonalHom, MvPolynomial.coe_eval₂Hom, one_mul] using hf.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (t ^ w i) * MvPolynomial.X i)
    (fun c => MvPolynomial.isHomogeneous_C _ c)
    (fun i => MvPolynomial.isHomogeneous_C_mul_X (t ^ w i) i)

theorem exists_common_homogeneousTaylor_degeneration {ι : Type*}
    (I : Finset ι) (φ : ι → MvPowerSeries (Fin n) K) (p : ι → Fin n →₀ ℕ) (d : ℕ)
    (hp : ∀ l ∈ I, IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) (φ l) (p l))
    (hd : ∀ l ∈ I, (p l).degree = d) :
    ∃ w : Fin n → ℕ, (∀ i, 0 < w i) ∧ ∀ l ∈ I,
      (homogeneousTaylorForm d (φ l)).IsHomogeneous d ∧
      (homogeneousTaylorForm d (φ l)).totalDegree = d ∧
      (homogeneousParameterFamily w (p l) (homogeneousTaylorForm d (φ l))).IsHomogeneous d ∧
      MvPolynomial.map (Polynomial.evalRingHom 0)
        (homogeneousParameterFamily w (p l) (homogeneousTaylorForm d (φ l))) =
          MvPolynomial.monomial (p l) (MvPowerSeries.coeff (p l) (φ l)) ∧
      MvPolynomial.map (Polynomial.evalRingHom 1)
        (homogeneousParameterFamily w (p l) (homogeneousTaylorForm d (φ l))) =
          homogeneousTaylorForm d (φ l) ∧
      ∀ t : K, t ≠ 0 →
        MvPolynomial.C (t ^ polynomialExponentWeight w (p l)) *
          MvPolynomial.map (Polynomial.evalRingHom t)
            (homogeneousParameterFamily w (p l) (homogeneousTaylorForm d (φ l))) =
              polynomialDiagonalHom w t (homogeneousTaylorForm d (φ l)) ∧
        MvPolynomial.map (Polynomial.evalRingHom t)
          (homogeneousParameterFamily w (p l) (homogeneousTaylorForm d (φ l))) ≠ 0 := by
  classical
  let f := fun l => homogeneousTaylorForm d (φ l)
  have hinitial : ∀ l ∈ I, IsPolynomialLexInitial (f l) (p l) := by
    intro l hl
    dsimp [f]
    rw [← hd l hl]
    exact homogeneousTaylorForm_lexInitial (hp l hl)
  obtain ⟨w, hw, hfamily⟩ := exists_common_polynomial_degeneration I f p hinitial
  refine ⟨w, hw, ?_⟩
  intro l hl
  have hhom : (f l).IsHomogeneous d := homogeneousTaylorForm_isHomogeneous d (φ l)
  have hdegree : (f l).totalDegree = d := by
    dsimp [f]
    rw [← hd l hl]
    exact homogeneousTaylorForm_totalDegree (hp l hl)
  obtain ⟨hzero, _, hone, hnonzero⟩ := hfamily l hl
  refine ⟨hhom, hdegree, homogeneousParameterFamily_isHomogeneous w (p l) hhom, ?_, ?_, ?_⟩
  · rw [homogeneousParameterFamily_baseChange, map_zero, hzero]
    congr 1
    simp [f, homogeneousTaylorForm_coeff, hd l hl]
  · rw [homogeneousParameterFamily_baseChange, map_one]
    exact hone
  · intro t ht
    rw [homogeneousParameterFamily_baseChange]
    exact hnonzero t ht

theorem equality_slice_homogeneousTaylor_form
    (φ : MvPowerSeries (Fin n) K) (β : Fin n →₀ ℕ) {r j D a b : ℕ} {δ : ℚ}
    (k l : Fin n) (hr : 0 < r) (hj : 0 < j) (hD : 0 < D) (ha : 0 < a) (hb : 0 < b)
    (hφ : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ β)
    (hβ : ∀ i, (β i : ℚ) / ((D : ℚ) * j) =
      rationalSliceTarget (fun _ => (b : ℚ) / a) δ k l i) :
    let h := equalityHeight r j D b
    (φ ^ (r * a)).order = (n * h : ℕ) ∧
    (homogeneousTaylorForm (n * h) (φ ^ (r * a))).IsHomogeneous (n * h) ∧
    (homogeneousTaylorForm (n * h) (φ ^ (r * a))).totalDegree = n * h ∧
    IsPolynomialLexInitial (homogeneousTaylorForm (n * h) (φ ^ (r * a))) ((r * a) • β) := by
  have hp := initialMonomial_pow (MonomialOrder.degLex (σ := Fin n)) hφ (r * a)
  have hdegree : ((r * a) • β).degree = n * equalityHeight r j D b := by
    rw [Finsupp.degree_eq_sum]
    exact equality_slice_totalDegree β k l hr hj hD ha hb hβ
  dsimp only
  refine ⟨?_, homogeneousTaylorForm_isHomogeneous _ _, ?_, ?_⟩
  · rw [degreeLex_initial_order hp, hdegree]
  · rw [← hdegree]
    exact homogeneousTaylorForm_totalDegree hp
  · rw [← hdegree]
    exact homogeneousTaylorForm_lexInitial hp

end MixedFujita
