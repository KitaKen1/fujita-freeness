/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.WeightedTaylorOrder
public import Mathlib.Order.Minimal
public import Mathlib.Order.Antichain
public import Mathlib.Tactic.Linarith

/-!
Infinite power-series supports reduce to finitely many componentwise minimal
exponents by Dickson's lemma. Nonnegative perturbation weights preserve that
domination. The lexicographic initial exponent gives a uniform first-order
lower bound for the perturbed cost, with a quadratic upper remainder supplied
by the same exponent. This establishes the algebraic perturbation step;
the geometric discrepancy/moment inequality remains separate.
-/

@[expose] public section

namespace MixedFujita

theorem exists_finite_dominating_exponents {σ : Type*} [Finite σ]
    (S : Set (σ →₀ ℕ)) :
    ∃ E : Finset (σ →₀ ℕ), (↑E : Set (σ →₀ ℕ)) ⊆ S ∧
      ∀ a ∈ S, ∃ b ∈ E, b ≤ a := by
  classical
  have hfinite : {a | Minimal (· ∈ S) a}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (· ∈ S))
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · intro a ha
    exact (hfinite.mem_toFinset.mp ha).1
  · intro a ha
    obtain ⟨b, hba, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ S) a ha
    exact ⟨b, hfinite.mem_toFinset.mpr hb, hba⟩

theorem finite_lex_perturbation_lower_bound {ι : Type*}
    (E : Finset ι) (A B C : ι → ℝ) (p : ι)
    (hBp : 0 ≤ B p) (hB : ∀ q ∈ E, 0 ≤ B q) (hC : ∀ q ∈ E, 0 ≤ C q)
    (hA : ∀ q ∈ E, A p ≤ A q)
    (hAB : ∀ q ∈ E, A q = A p → B p ≤ B q) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → ∀ q ∈ E,
      A p + ε * B p ≤ A q + ε * B q + ε ^ 2 * C q := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert q E hq ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
      (fun x hx => hB x (Finset.mem_insert_of_mem hx))
      (fun x hx => hC x (Finset.mem_insert_of_mem hx))
      (fun x hx => hA x (Finset.mem_insert_of_mem hx))
      (fun x hx => hAB x (Finset.mem_insert_of_mem hx))
    let η := if A p < A q then (A q - A p) / (B p + 1) else 1
    have hden : 0 < B p + 1 := by linarith
    have hη : 0 < η := by
      dsimp [η]
      split_ifs with h
      · exact div_pos (sub_pos.mpr h) hden
      · norm_num
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro ε hε hεδ x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      have hBq := hB q (Finset.mem_insert_self _ _)
      have hCq := hC q (Finset.mem_insert_self _ _)
      have hAq := hA q (Finset.mem_insert_self _ _)
      have hquad : 0 ≤ ε ^ 2 * C q := mul_nonneg (sq_nonneg _) hCq
      by_cases heq : A q = A p
      · have hlinear := mul_le_mul_of_nonneg_left
          (hAB q (Finset.mem_insert_self _ _) heq) hε
        linarith
      · have hgap : A p < A q := lt_of_le_of_ne hAq (Ne.symm heq)
        have hεη : ε ≤ (A q - A p) / (B p + 1) := by
          simpa only [η, ite_eq_left hgap] using (le_min_iff.mp hεδ).2
        have hbudget := (le_div_iff₀ hden).mp hεη
        have hpositive := mul_nonneg hε hBq
        nlinarith
    · exact hbound ε hε (le_min_iff.mp hεδ).1 x hx

variable {σ K : Type*} [Fintype σ] [Field K]

noncomputable def perturbedExponentCost (w : σ → ℝ) (v u : σ → ℕ) (ε : ℝ)
    (a : σ →₀ ℕ) : ℝ :=
  realExponentWeight w a + ε * (natExponentDegree v a : ℝ) +
    ε ^ 2 * (natExponentDegree u a : ℝ)

theorem perturbedExponentCost_eq_realWeight (w : σ → ℝ) (v u : σ → ℕ) (ε : ℝ)
    (a : σ →₀ ℕ) :
    perturbedExponentCost w v u ε a =
      realExponentWeight (fun i => w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ)) a := by
  simp [perturbedExponentCost, realExponentWeight, natExponentDegree,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem perturbedExponentCost_monotone (w : σ → ℝ) (v u : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) {ε : ℝ} (hε : 0 ≤ ε) :
    Monotone (perturbedExponentCost w v u ε) := by
  intro a b hab
  apply add_le_add
  · apply add_le_add (realExponentWeight_monotone w hw hab)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast natExponentDegree_monotone v hab) hε
  · exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast natExponentDegree_monotone u hab) (sq_nonneg _)

theorem exists_minimal_perturbedExponentCost (m : MonomialOrder σ)
    (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {ε : ℝ} (hε : 0 ≤ ε) {φ : MvPowerSeries σ K} (hφ : φ ≠ 0) :
    ∃ q, MvPowerSeries.coeff q φ ≠ 0 ∧ ∀ r, MvPowerSeries.coeff r φ ≠ 0 →
      perturbedExponentCost w v u ε q ≤ perturbedExponentCost w v u ε r := by
  let wε := fun i => w i + ε * (v i : ℝ) + ε ^ 2 * (u i : ℝ)
  have hwε : ∀ i, 0 ≤ wε i := fun i =>
    add_nonneg (add_nonneg (hw i) (mul_nonneg hε (Nat.cast_nonneg _)))
      (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  obtain ⟨q, hq⟩ := exists_initialMonomial (weightedMonomialOrder m wε (fun _ => 0) hwε) hφ
  refine ⟨q, hq.1, ?_⟩
  intro r hr
  rw [perturbedExponentCost_eq_realWeight, perturbedExponentCost_eq_realWeight]
  exact initialMonomial_realWeight_min m wε (fun _ => 0) hwε hq hr

theorem powerSeries_support_perturbation_lower_bound
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → ∀ q, MvPowerSeries.coeff q φ ≠ 0 →
      realExponentWeight w p + ε * (natExponentDegree v p : ℝ) ≤
        perturbedExponentCost w v u ε q := by
  obtain ⟨E, hES, hdom⟩ := exists_finite_dominating_exponents
    {q | MvPowerSeries.coeff q φ ≠ 0}
  obtain ⟨δ, hδ, hbound⟩ := finite_lex_perturbation_lower_bound E
    (realExponentWeight w) (fun q => (natExponentDegree v q : ℝ))
    (fun q => (natExponentDegree u q : ℝ)) p (Nat.cast_nonneg _) 
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (fun q hq => initialMonomial_realWeight_min m w v hw hp (hES hq))
    (fun q hq heq => by
      exact_mod_cast initialMonomial_natDegree_min m w v hw hp (hES hq) heq)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ q hq
  obtain ⟨b, hb, hbq⟩ := hdom q hq
  exact (hbound ε hε hεδ b hb).trans (perturbedExponentCost_monotone w v u hw hε hbq)

/-- Any minimizing exponent has a quadratic remainder controlled by the explicit initial exponent. -/
theorem powerSeries_perturbation_sandwich
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → ∀ q,
      MvPowerSeries.coeff q φ ≠ 0 →
      perturbedExponentCost w v u ε q ≤ perturbedExponentCost w v u ε p →
        realExponentWeight w p + ε * (natExponentDegree v p : ℝ) ≤
          perturbedExponentCost w v u ε q ∧
        perturbedExponentCost w v u ε q ≤
          realExponentWeight w p + ε * (natExponentDegree v p : ℝ) +
            ε ^ 2 * (natExponentDegree u p : ℝ) := by
  obtain ⟨δ, hδ, hbound⟩ := powerSeries_support_perturbation_lower_bound m w v u hw hp
  exact ⟨δ, hδ, fun ε hε hεδ q hq hmin => ⟨hbound ε hε hεδ q hq, hmin⟩⟩

theorem powerSeries_perturbation_firstVariation_bound
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε ≤ δ → ∀ q,
      MvPowerSeries.coeff q φ ≠ 0 →
      perturbedExponentCost w v u ε q ≤ perturbedExponentCost w v u ε p →
        (natExponentDegree v p : ℝ) ≤
          (perturbedExponentCost w v u ε q - realExponentWeight w p) / ε ∧
        (perturbedExponentCost w v u ε q - realExponentWeight w p) / ε ≤
          (natExponentDegree v p : ℝ) + ε * (natExponentDegree u p : ℝ) := by
  obtain ⟨δ, hδ, hbound⟩ := powerSeries_perturbation_sandwich m w v u hw hp
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ q hq hmin
  obtain ⟨hlower, hupper⟩ := hbound ε hε.le hεδ q hq hmin
  constructor
  · apply (le_div_iff₀ hε).mpr
    nlinarith
  · apply (div_le_iff₀ hε).mpr
    nlinarith

end MixedFujita
