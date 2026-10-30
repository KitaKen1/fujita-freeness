/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupJetRemainder
public import MixedFujita.TaylorLinearCombination
public import MixedFujita.LocalAdicOrder

/-!
Canonical leading jets of actual local-ring elements in compatible Taylor coordinates.
The homogeneous leading form itself is the required polynomial jet: its pullback differs
from the original element by the next maximal-ideal power. This removes the supplied jet
representative and jet-remainder hypotheses from exceptional restriction calculations.
-/

@[expose] public section
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R A : Type*} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
  [CommRing A] {n : ℕ}

omit [IsLocalRing R] in
theorem taylorCoordinates_polynomial (ψ : MvPolynomial (Fin n) K →ₐ[K] R)
    (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (g : MvPolynomial (Fin n) K) : T (ψ g) = (g : MvPowerSeries (Fin n) K) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    have hψ : ψ (MvPolynomial.C c) = algebraMap K R c := ψ.commutes c
    have hT : T (algebraMap K R c) = MvPowerSeries.C c := T.commutes c
    rw [hψ, hT, MvPolynomial.coe_C]
  | add g h hg hh => simp only [map_add, MvPolynomial.coe_add, hg, hh]
  | mul_X g i hg => simp only [map_mul, MvPolynomial.coe_mul, MvPolynomial.coe_X, hg, hX]

theorem homogeneousTaylorForm_coe_order_ge (m : ℕ) (φ : MvPowerSeries (Fin n) K) :
    (m : ℕ∞) ≤ (homogeneousTaylorForm m φ : MvPowerSeries (Fin n) K).order := by
  apply MvPowerSeries.nat_le_order
  intro p hp
  rw [MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff, ite_eq_right (ne_of_lt hp)]

theorem homogeneousTaylorForm_idempotent (m : ℕ) (φ : MvPowerSeries (Fin n) K) :
    homogeneousTaylorForm m (homogeneousTaylorForm m φ : MvPowerSeries (Fin n) K) =
      homogeneousTaylorForm m φ := by
  ext p
  rw [homogeneousTaylorForm_coeff, MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff]
  split_ifs <;> rfl

theorem localTaylorCoordinate_mem_maximalIdeal
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r) (i : Fin n) :
    ψ (MvPolynomial.X i) ∈ IsLocalRing.maximalIdeal R := by
  have h : (1 : ℕ∞) ≤ localAdicOrder R (ψ (MvPolynomial.X i)) := by
    rw [← hord, hX, MvPowerSeries.one_le_order_iff_constCoeff_eq_zero]
    simp
  simpa only [pow_one] using (localAdicOrder_nat_le_iff (ψ (MvPolynomial.X i)) 1).mp h

theorem localLeadingJet_mem_pow (ψ : MvPolynomial (Fin n) K →ₐ[K] R)
    (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    s - ψ (homogeneousTaylorForm m (T s)) ∈ IsLocalRing.maximalIdeal R ^ (m + 1) := by
  rw [← localAdicOrder_nat_le_iff, ← hord, map_sub, taylorCoordinates_polynomial ψ T hX]
  exact homogeneousTaylorForm_remainder_order m (T s) hs

theorem localLeadingJet_strictTransform_exceptional
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (β : R →+* A) (τ : MvPolynomial (Fin n) K →+* A) (k : Fin n)
    (hI : (IsLocalRing.maximalIdeal R).map β = Ideal.span {τ (MvPolynomial.X k)})
    (hcomp : ∀ g, β (ψ g) = τ (polynomialPointBlowupMap k g))
    (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    ∃ q : A, β s = τ (MvPolynomial.X k) ^ m * q ∧
      Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
        pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
          (homogeneousTaylorForm m (T s))) := by
  obtain ⟨q, hq, hres⟩ := polynomialPointBlowupStrictTransform_jet_remainder
    β (IsLocalRing.maximalIdeal R) τ k hI s (ψ (homogeneousTaylorForm m (T s))) m
    (homogeneousTaylorForm m (T s)) (localLeadingJet_mem_pow ψ T hX hord s m hs)
    (hcomp _) (homogeneousTaylorForm_coe_order_ge m (T s))
  rw [homogeneousTaylorForm_idempotent] at hres
  exact ⟨q, hq, hres⟩

end MixedFujita
