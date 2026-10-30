/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IntegerLexWeights
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
An actual polynomial family with monomial special fiber, using one positive
integer weight vector for a finite collection. Nonzero fibers are rescaled
diagonal substitutions. This is an algebraic construction; projective
families, properness, and log canonical threshold specialization are separate.
-/

@[expose] public section

namespace MixedFujita

def polynomialExponentWeight {n : ℕ} (w : Fin n → ℕ) (p : Fin n →₀ ℕ) : ℕ :=
  ∑ i, w i * p i

def IsPolynomialLexInitial {n : ℕ} {K : Type*} [Field K]
    (f : MvPolynomial (Fin n) K) (p : Fin n →₀ ℕ) : Prop :=
  p ∈ f.support ∧ ∀ q ∈ f.support, q ≠ p →
    (MonomialOrder.lex (σ := Fin n)).toSyn p < MonomialOrder.lex.toSyn q

theorem polynomialLexInitial_iff_powerSeries {n : ℕ} {K : Type*} [Field K]
    (f : MvPolynomial (Fin n) K) (p : Fin n →₀ ℕ) :
    IsPolynomialLexInitial f p ↔
      IsInitialMonomial (MonomialOrder.lex (σ := Fin n)) (f : MvPowerSeries (Fin n) K) p := by
  classical
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨by simpa only [MvPolynomial.coeff_coe] using MvPolynomial.mem_support_iff.mp hp, ?_⟩
    intro q hq
    by_contra hn
    have hs : q ∈ f.support := MvPolynomial.mem_support_iff.mpr
      (by simpa only [MvPolynomial.coeff_coe] using hn)
    have hne : q ≠ p := by
      intro h
      subst q
      exact lt_irrefl _ hq
    exact lt_asymm (hmin q hs hne) hq
  · rintro ⟨hp, hmin⟩
    refine ⟨MvPolynomial.mem_support_iff.mpr (by simpa only [MvPolynomial.coeff_coe] using hp), ?_⟩
    intro q hq hne
    rcases lt_trichotomy (MonomialOrder.lex.toSyn p) (MonomialOrder.lex.toSyn q) with h | h | h
    · exact h
    · exact False.elim (hne (MonomialOrder.lex.toSyn.injective h).symm)
    · have hzero := hmin q h
      rw [MvPolynomial.coeff_coe] at hzero
      exact False.elim (MvPolynomial.mem_support_iff.mp hq hzero)

theorem exists_common_polynomial_initial_weights {n : ℕ} {K ι : Type*} [Field K]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ l ∈ I, IsPolynomialLexInitial (f l) (p l)) :
    ∃ w : Fin n → ℕ, (∀ i, 0 < w i) ∧ ∀ l ∈ I, ∀ q ∈ (f l).support,
      q ≠ p l → polynomialExponentWeight w (p l) < polynomialExponentWeight w q := by
  classical
  let S := I.biUnion (fun l => (f l).support)
  obtain ⟨w, hw, horder⟩ := exists_common_positive_integer_lex_weights S
  refine ⟨w, hw, ?_⟩
  intro l hl q hq hne
  apply horder (p l) (Finset.mem_biUnion.mpr ⟨l, hl, (hp l hl).1⟩)
    q (Finset.mem_biUnion.mpr ⟨l, hl, hq⟩)
  exact (hp l hl).2 q hq hne

noncomputable def weightedPolynomialFamily {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) :
    Polynomial (MvPolynomial (Fin n) K) :=
  ∑ q ∈ f.support, Polynomial.monomial
    (polynomialExponentWeight w q - polynomialExponentWeight w p)
    (MvPolynomial.monomial q (f.coeff q))

theorem weightedPolynomialFamily_at_one {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) :
    (weightedPolynomialFamily w p f).eval 1 = f := by
  classical
  simp only [weightedPolynomialFamily, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    one_pow, mul_one]
  exact (MvPolynomial.as_sum f).symm

theorem weightedPolynomialFamily_at_zero {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K)
    (hp : p ∈ f.support)
    (hw : ∀ q ∈ f.support, q ≠ p →
      polynomialExponentWeight w p < polynomialExponentWeight w q) :
    (weightedPolynomialFamily w p f).eval 0 = MvPolynomial.monomial p (f.coeff p) := by
  classical
  simp only [weightedPolynomialFamily, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [Finset.sum_eq_single_of_mem p hp]
  · simp
  · intro q hq hne
    have hpos : 0 < polynomialExponentWeight w q - polynomialExponentWeight w p :=
      Nat.sub_pos_of_lt (hw q hq hne)
    simp [zero_pow hpos.ne']

noncomputable def polynomialDiagonalHom {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (t : K) :
    MvPolynomial (Fin n) K →+* MvPolynomial (Fin n) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.C (t ^ w i) * MvPolynomial.X i)

theorem polynomialDiagonalHom_monomial {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (t c : K) (p : Fin n →₀ ℕ) :
    polynomialDiagonalHom w t (MvPolynomial.monomial p c) =
      MvPolynomial.C (t ^ polynomialExponentWeight w p) * MvPolynomial.monomial p c := by
  classical
  rw [polynomialDiagonalHom, MvPolynomial.eval₂Hom_monomial,
    Finsupp.prod_fintype p _ (fun i => by simp)]
  simp only [mul_pow, ← map_pow, Finset.prod_mul_distrib, ← map_prod,
    ← pow_mul, Finset.prod_pow_eq_pow_sum, polynomialExponentWeight]
  rw [MvPolynomial.monomial_eq, ← Finsupp.prod_pow]
  ring

theorem weightedPolynomialFamily_scaled_parameter {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) (t : K)
    (hw : ∀ q ∈ f.support, polynomialExponentWeight w p ≤ polynomialExponentWeight w q) :
    MvPolynomial.C (t ^ polynomialExponentWeight w p) *
      (weightedPolynomialFamily w p f).eval (MvPolynomial.C t) = polynomialDiagonalHom w t f := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum f]
  simp only [weightedPolynomialFamily, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    map_sum, polynomialDiagonalHom_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [mul_comm (MvPolynomial.monomial q (f.coeff q)), ← mul_assoc,
    ← map_pow, ← map_mul, ← pow_add, Nat.add_sub_of_le (hw q hq)]

theorem polynomialDiagonalHom_inverse {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (f : MvPolynomial (Fin n) K) :
    polynomialDiagonalHom w t⁻¹ (polynomialDiagonalHom w t f) = f := by
  have h : (polynomialDiagonalHom w t⁻¹).comp (polynomialDiagonalHom w t) =
      RingHom.id (MvPolynomial (Fin n) K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [polynomialDiagonalHom]
    · intro i
      simp only [RingHom.comp_apply, RingHom.id_apply, polynomialDiagonalHom,
        MvPolynomial.eval₂Hom_X']
      rw [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
        ← mul_assoc, ← MvPolynomial.C_mul, ← mul_pow]
      simp [ht]
  exact RingHom.congr_fun h f

theorem polynomialDiagonalHom_injective {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) : Function.Injective (polynomialDiagonalHom w t) := by
  intro f g h
  have h' := congrArg (polynomialDiagonalHom w t⁻¹) h
  simpa only [polynomialDiagonalHom_inverse w ht] using h'

noncomputable def polynomialDiagonalEquiv {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    MvPolynomial (Fin n) K ≃+* MvPolynomial (Fin n) K :=
  RingEquiv.ofBijective (polynomialDiagonalHom w t)
    ⟨polynomialDiagonalHom_injective w ht, fun f => ⟨polynomialDiagonalHom w t⁻¹ f, by
      have h := polynomialDiagonalHom_inverse w (inv_ne_zero ht) f
      rw [inv_inv] at h
      exact h⟩⟩

theorem weightedPolynomialFamily_nonzero_fiber {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (p : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) K) {t : K}
    (ht : t ≠ 0) (hf : f ≠ 0)
    (hw : ∀ q ∈ f.support, polynomialExponentWeight w p ≤ polynomialExponentWeight w q) :
    (weightedPolynomialFamily w p f).eval (MvPolynomial.C t) ≠ 0 := by
  intro hzero
  have h := weightedPolynomialFamily_scaled_parameter w p f t hw
  rw [hzero, mul_zero] at h
  apply hf
  apply polynomialDiagonalHom_injective w ht
  simpa only [map_zero] using h.symm

/-- One weight vector and one family per polynomial, simultaneously, with
nonzero monomial special fibers and invertible diagonal nonzero fibers. -/
theorem exists_common_polynomial_degeneration {n : ℕ} {K ι : Type*} [Field K]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (p : ι → Fin n →₀ ℕ)
    (hp : ∀ l ∈ I, IsPolynomialLexInitial (f l) (p l)) :
    ∃ w : Fin n → ℕ, (∀ i, 0 < w i) ∧ ∀ l ∈ I,
      (weightedPolynomialFamily w (p l) (f l)).eval 0 =
        MvPolynomial.monomial (p l) ((f l).coeff (p l)) ∧
      (weightedPolynomialFamily w (p l) (f l)).eval 0 ≠ 0 ∧
      (weightedPolynomialFamily w (p l) (f l)).eval 1 = f l ∧
      ∀ t : K, t ≠ 0 →
        MvPolynomial.C (t ^ polynomialExponentWeight w (p l)) *
          (weightedPolynomialFamily w (p l) (f l)).eval (MvPolynomial.C t) =
            polynomialDiagonalHom w t (f l) ∧
        (weightedPolynomialFamily w (p l) (f l)).eval (MvPolynomial.C t) ≠ 0 := by
  classical
  obtain ⟨w, hw, hmin⟩ := exists_common_polynomial_initial_weights I f p hp
  refine ⟨w, hw, ?_⟩
  intro l hl
  have hp' := (hp l hl).1
  have hzero := weightedPolynomialFamily_at_zero w (p l) (f l) hp' (hmin l hl)
  have hcoeff : (f l).coeff (p l) ≠ 0 := MvPolynomial.mem_support_iff.mp hp'
  have hf : f l ≠ 0 := by
    intro h
    simp [h] at hcoeff
  have hle : ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q := by
    intro q hq
    by_cases heq : q = p l
    · simp [heq]
    · exact (hmin l hl q hq heq).le
  refine ⟨hzero, ?_, weightedPolynomialFamily_at_one w (p l) (f l), ?_⟩
  · rw [hzero]
    exact MvPolynomial.monomial_eq_zero.not.mpr hcoeff
  · intro t ht
    exact ⟨weightedPolynomialFamily_scaled_parameter w (p l) (f l) t hle,
      weightedPolynomialFamily_nonzero_fiber w (p l) (f l) ht hf hle⟩

end MixedFujita
