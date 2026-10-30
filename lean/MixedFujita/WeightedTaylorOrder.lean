/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.WeightedMonomialOrder
public import MixedFujita.PowerSeriesExponents
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
The manuscript's order: crossing weight, tangential degree, fixed monomial
tie order. Tangential variables have zero crossing weight. Nonzero power
series have an initial exponent attaining the least crossing weight and,
among exponents of that weight, the least tangential degree.
These are algebraic facts about MvPowerSeries, not geometric Taylor-map
construction or the discrepancy bound for the perturbation.
-/

@[expose] public section

namespace MixedFujita

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

def crossingVariableWeight (w : σ → ℝ) : σ ⊕ τ → ℝ := Sum.elim w (fun _ => 0)

def tangentVariableDegree : σ ⊕ τ → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

omit [Fintype σ] [Fintype τ] in
theorem crossingVariableWeight_nonneg (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∀ i : σ ⊕ τ, 0 ≤ crossingVariableWeight w i := by
  rintro (i | i)
  · exact hw i
  · exact le_rfl

theorem crossingExponentWeight_eq (w : σ → ℝ) (a : (σ ⊕ τ) →₀ ℕ) :
    realExponentWeight (crossingVariableWeight w) a = ∑ i, w i * (a (Sum.inl i) : ℝ) := by
  simp [realExponentWeight, crossingVariableWeight, Fintype.sum_sum_type]

theorem tangentExponentDegree_eq (a : (σ ⊕ τ) →₀ ℕ) :
    natExponentDegree (tangentVariableDegree (σ := σ) (τ := τ)) a =
      ∑ i : τ, a (Sum.inr i) := by
  simp [natExponentDegree, tangentVariableDegree, Fintype.sum_sum_type]

noncomputable def crossingTangentMonomialOrder (m : MonomialOrder (σ ⊕ τ))
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) : MonomialOrder (σ ⊕ τ) :=
  weightedMonomialOrder m (crossingVariableWeight w) tangentVariableDegree
    (crossingVariableWeight_nonneg w hw)

theorem crossingTangentMonomialOrder_lt_iff (m : MonomialOrder (σ ⊕ τ))
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : (σ ⊕ τ) →₀ ℕ) :
    (crossingTangentMonomialOrder m w hw).toSyn a <
      (crossingTangentMonomialOrder m w hw).toSyn b ↔
      (∑ i, w i * (a (Sum.inl i) : ℝ)) < (∑ i, w i * (b (Sum.inl i) : ℝ)) ∨
        (∑ i, w i * (a (Sum.inl i) : ℝ)) = (∑ i, w i * (b (Sum.inl i) : ℝ)) ∧
          ((∑ i : τ, a (Sum.inr i)) < (∑ i : τ, b (Sum.inr i)) ∨
            (∑ i : τ, a (Sum.inr i)) = (∑ i : τ, b (Sum.inr i)) ∧
              m.toSyn a < m.toSyn b) := by
  change (weightedMonomialOrder m (crossingVariableWeight w) tangentVariableDegree
    (crossingVariableWeight_nonneg w hw)).toSyn a <
      (weightedMonomialOrder m (crossingVariableWeight w) tangentVariableDegree
        (crossingVariableWeight_nonneg w hw)).toSyn b ↔ _
  rw [weightedMonomialOrder_lt_iff]
  simp only [crossingExponentWeight_eq, tangentExponentDegree_eq]

/-- The final tie order is constructed, rather than assumed to exist. -/
noncomputable def paperTaylorMonomialOrder (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    MonomialOrder (σ ⊕ τ) :=
  crossingTangentMonomialOrder (finiteLexMonomialOrder (σ ⊕ τ)) w hw

variable {K : Type*} [Field K]

theorem initialMonomial_realWeight_min {ι : Type*} [Fintype ι]
    (m : MonomialOrder ι) (w : ι → ℝ) (v : ι → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries ι K} {p : ι →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p)
    {q : ι →₀ ℕ} (hq : MvPowerSeries.coeff q φ ≠ 0) :
    realExponentWeight w p ≤ realExponentWeight w q := by
  by_contra h
  exact hq (hp.2 q ((weightedMonomialOrder_lt_iff m w v hw q p).mpr
    (Or.inl (lt_of_not_ge h))))

theorem initialMonomial_natDegree_min {ι : Type*} [Fintype ι]
    (m : MonomialOrder ι) (w : ι → ℝ) (v : ι → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries ι K} {p : ι →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p)
    {q : ι →₀ ℕ} (hq : MvPowerSeries.coeff q φ ≠ 0)
    (hweight : realExponentWeight w q = realExponentWeight w p) :
    natExponentDegree v p ≤ natExponentDegree v q := by
  by_contra h
  exact hq (hp.2 q ((weightedMonomialOrder_lt_iff m w v hw q p).mpr
    (Or.inr ⟨hweight, Or.inl (lt_of_not_ge h)⟩)))

theorem initialMonomial_crossingWeight_min (m : MonomialOrder (σ ⊕ τ))
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries (σ ⊕ τ) K} {p : (σ ⊕ τ) →₀ ℕ}
    (hp : IsInitialMonomial (crossingTangentMonomialOrder m w hw) φ p)
    {q : (σ ⊕ τ) →₀ ℕ} (hq : MvPowerSeries.coeff q φ ≠ 0) :
    (∑ i, w i * (p (Sum.inl i) : ℝ)) ≤ (∑ i, w i * (q (Sum.inl i) : ℝ)) := by
  have h := initialMonomial_realWeight_min m (crossingVariableWeight w)
    tangentVariableDegree (crossingVariableWeight_nonneg w hw) hp hq
  simpa only [crossingExponentWeight_eq] using h

theorem initialMonomial_tangentDegree_min (m : MonomialOrder (σ ⊕ τ))
    (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries (σ ⊕ τ) K} {p : (σ ⊕ τ) →₀ ℕ}
    (hp : IsInitialMonomial (crossingTangentMonomialOrder m w hw) φ p)
    {q : (σ ⊕ τ) →₀ ℕ} (hq : MvPowerSeries.coeff q φ ≠ 0)
    (hweight : (∑ i, w i * (q (Sum.inl i) : ℝ)) =
      (∑ i, w i * (p (Sum.inl i) : ℝ))) :
    (∑ i : τ, p (Sum.inr i)) ≤ (∑ i : τ, q (Sum.inr i)) := by
  have hweight' : realExponentWeight (crossingVariableWeight w) q =
      realExponentWeight (crossingVariableWeight w) p := by
    simpa only [crossingExponentWeight_eq] using hweight
  have h := initialMonomial_natDegree_min m (crossingVariableWeight w)
    tangentVariableDegree (crossingVariableWeight_nonneg w hw) hp hq hweight'
  simpa only [tangentExponentDegree_eq] using h

theorem exists_paperInitialMonomial (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries (σ ⊕ τ) K} (hφ : φ ≠ 0) :
    ∃ p, IsInitialMonomial (paperTaylorMonomialOrder w hw) φ p :=
  exists_initialMonomial _ hφ

end MixedFujita
