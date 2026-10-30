/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialDegeneration
public import MixedFujita.RationalSectionProducts
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
Extract the actual finite homogeneous Taylor polynomial. A degree-lex
initial exponent has degree equal to the power-series order, survives in
this polynomial, and becomes its lex initial exponent. Extraction respects
products at the lowest degrees. These statements concern actual power
series, not the construction of a geometric Taylor expansion.
-/

@[expose] public section

namespace MixedFujita

variable {σ K : Type*} [Finite σ] [Field K]

noncomputable def homogeneousTaylorForm (d : ℕ) :
    MvPowerSeries σ K →ₗ[K] MvPolynomial σ K :=
  (MvPowerSeries.truncTotal (d + 1)).comp (MvPowerSeries.homogeneousComponent d)

theorem homogeneousTaylorForm_coeff (d : ℕ) (φ : MvPowerSeries σ K) (p : σ →₀ ℕ) :
    (homogeneousTaylorForm d φ).coeff p =
      if p.degree = d then MvPowerSeries.coeff p φ else 0 := by
  classical
  simp only [homogeneousTaylorForm, LinearMap.comp_apply,
    MvPowerSeries.coeff_truncTotal_eq_ite, MvPowerSeries.coeff_homogeneousComponent]
  by_cases h : p.degree = d
  · simp [h]
  · simp [h]

theorem homogeneousTaylorForm_coe (d : ℕ) (φ : MvPowerSeries σ K) :
    (homogeneousTaylorForm d φ : MvPowerSeries σ K) = φ.homogeneousComponent d := by
  apply MvPowerSeries.ext
  intro p
  simp only [MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff,
    MvPowerSeries.coeff_homogeneousComponent]

theorem homogeneousTaylorForm_isHomogeneous (d : ℕ) (φ : MvPowerSeries σ K) :
    (homogeneousTaylorForm d φ).IsHomogeneous d := by
  intro p hp
  have hd : p.degree = d := by
    by_contra h
    exact hp (by simp [homogeneousTaylorForm_coeff, h])
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd

theorem homogeneousTaylorForm_nonzero (φ : MvPowerSeries σ K) (p : σ →₀ ℕ)
    (hp : MvPowerSeries.coeff p φ ≠ 0) : homogeneousTaylorForm p.degree φ ≠ 0 := by
  intro hzero
  have h := congrArg (fun f : MvPolynomial σ K => f.coeff p) hzero
  simp [homogeneousTaylorForm_coeff] at h
  exact hp h

theorem homogeneousTaylorForm_mul (φ ψ : MvPowerSeries σ K) (d e : ℕ)
    (hφ : (d : ℕ∞) ≤ φ.order) (hψ : (e : ℕ∞) ≤ ψ.order) :
    homogeneousTaylorForm (d + e) (φ * ψ) =
      homogeneousTaylorForm d φ * homogeneousTaylorForm e ψ := by
  apply MvPolynomial.coe_injective σ K
  rw [MvPolynomial.coe_mul, homogeneousTaylorForm_coe, homogeneousTaylorForm_coe,
    homogeneousTaylorForm_coe]
  exact MvPowerSeries.homogeneousComponent_mul_of_le_order hφ hψ

theorem degreeLex_initial_order {n : ℕ} {φ : MvPowerSeries (Fin n) K} {p : Fin n →₀ ℕ}
    (hp : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ p) :
    φ.order = (p.degree : ℕ∞) := by
  apply MvPowerSeries.order_eq_nat.mpr
  refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
  intro q hq
  apply hp.2 q
  rw [MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  exact Or.inl hq

theorem homogeneousTaylorForm_lexInitial {n : ℕ}
    {φ : MvPowerSeries (Fin n) K} {p : Fin n →₀ ℕ}
    (hp : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ p) :
    IsPolynomialLexInitial (homogeneousTaylorForm p.degree φ) p := by
  apply (polynomialLexInitial_iff_powerSeries _ p).mpr
  refine ⟨?_, ?_⟩
  · simpa only [MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff, ite_true] using hp.1
  · intro q hq
    rw [MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff]
    by_cases hd : q.degree = p.degree
    · rw [ite_eq_left hd]
      apply hp.2 q
      rw [MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
      exact Or.inr ⟨hd, hq⟩
    · simp [hd]

theorem homogeneousTaylorForm_totalDegree {n : ℕ}
    {φ : MvPowerSeries (Fin n) K} {p : Fin n →₀ ℕ}
    (hp : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ p) :
    (homogeneousTaylorForm p.degree φ).totalDegree = p.degree :=
  (homogeneousTaylorForm_isHomogeneous _ _).totalDegree (homogeneousTaylorForm_nonzero φ p hp.1)

theorem degreeLex_initial_product_form {n : ℕ}
    {φ ψ : MvPowerSeries (Fin n) K} {p q : Fin n →₀ ℕ}
    (hp : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ p)
    (hq : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) ψ q) :
    homogeneousTaylorForm (p + q).degree (φ * ψ) =
      homogeneousTaylorForm p.degree φ * homogeneousTaylorForm q.degree ψ := by
  rw [map_add]
  apply homogeneousTaylorForm_mul
  · rw [degreeLex_initial_order hp]
  · rw [degreeLex_initial_order hq]

theorem degreeLex_initial_power_form {n : ℕ}
    {φ : MvPowerSeries (Fin n) K} {p : Fin n →₀ ℕ}
    (hp : IsInitialMonomial (MonomialOrder.degLex (σ := Fin n)) φ p) (r : ℕ) :
    homogeneousTaylorForm (r • p).degree (φ ^ r) =
      homogeneousTaylorForm p.degree φ ^ r := by
  induction r with
  | zero =>
    apply MvPolynomial.coe_injective (Fin n) K
    rw [homogeneousTaylorForm_coe]
    simp only [zero_nsmul, map_zero, pow_zero, MvPolynomial.coe_one]
    apply MvPowerSeries.ext
    intro q
    rw [MvPowerSeries.coeff_homogeneousComponent, MvPowerSeries.coeff_one]
    by_cases hq : q = 0
    · simp [hq]
    · have hd : q.degree ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
      simp [hq, hd]
  | succ r ih =>
    rw [succ_nsmul, map_add, pow_succ,
      homogeneousTaylorForm_mul _ _ _ _
        (by rw [degreeLex_initial_order (initialMonomial_pow _ hp r)])
        (by rw [degreeLex_initial_order hp]), ih, pow_succ]

end MixedFujita
