/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupExceptionalBaseChange
public import Mathlib.RingTheory.Ideal.Operations

/-!
An (m+1)-st order jet remainder vanishes on the exceptional divisor after division by
the m-th power of its equation. The hypotheses record the actual extension of the centre
ideal to a principal ideal. A second theorem combines this with the polynomial leading-form
calculation. Constructing these jet data for arbitrary Cartier germs remains separate.
-/

@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w

theorem pointBlowupStrictTransform_of_jet_remainder
    {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    (β : R →+* A) (I : Ideal R) (a : A) (hI : I.map β = Ideal.span {a})
    (s p : R) (m : ℕ) (hjet : s - p ∈ I ^ (m + 1))
    (t : A) (hp : β p = a ^ m * t) :
    ∃ q : A, β s = a ^ m * q ∧
      Ideal.Quotient.mk (Ideal.span {a}) q = Ideal.Quotient.mk (Ideal.span {a}) t := by
  have hr : β (s - p) ∈ Ideal.span {a ^ (m + 1)} := by
    rw [← Ideal.span_singleton_pow, ← hI, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem β hjet
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hr
  refine ⟨t + a * r, ?_, ?_⟩
  · calc
      β s = β p + β (s - p) := by rw [map_sub]; ring
      _ = a ^ m * (t + a * r) := by rw [hp, hr, pow_succ]; ring
  · have ha : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    simp only [map_add, map_mul, ha, zero_mul, add_zero]

theorem polynomialPointBlowupStrictTransform_jet_remainder
    {K : Type u} [Field K] {R : Type v} [CommRing R] {A : Type w} [CommRing A] {n : ℕ}
    (β : R →+* A) (I : Ideal R) (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n)
    (hI : I.map β = Ideal.span {τ (MvPolynomial.X k)})
    (s p : R) (m : ℕ) (g : MvPolynomial (Fin n) K)
    (hjet : s - p ∈ I ^ (m + 1)) (hp : β p = τ (polynomialPointBlowupMap k g))
    (hg : (m : ℕ∞) ≤ (g : MvPowerSeries (Fin n) K).order) :
    ∃ q : A, β s = τ (MvPolynomial.X k) ^ m * q ∧
      Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
        pointBlowupExceptionalEvaluation τ k
          (projectiveDehomogenize K k (homogeneousTaylorForm m (g : MvPowerSeries (Fin n) K))) := by
  obtain ⟨q, hq, hres⟩ := pointBlowupStrictTransform_of_jet_remainder
    β I (τ (MvPolynomial.X k)) hI s p m hjet
    (τ (polynomialPointBlowupStrictTransform k m g))
    (hp.trans (polynomialPointBlowupStrictTransform_baseChange_factor τ k m g hg))
  exact ⟨q, hq, hres.trans
    (polynomialPointBlowupStrictTransform_baseChange_exceptional τ k m g hg)⟩

end MixedFujita
