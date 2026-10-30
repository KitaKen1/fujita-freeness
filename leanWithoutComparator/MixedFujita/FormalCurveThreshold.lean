/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartThreshold
public import MixedFujita.JacobianCoordinateChange

/-!
In one variable, the full formal-test threshold condition is exactly an ordinary order bound.
The Jacobian inequality proves sufficiency for any number of variables. With one variable,
the identity test of weight one proves necessity. Thus the actual ProjectiveThresholdCondition
for binary forms is equivalent to ordinary chart orders at every point, with no formal-test
quantifiers remaining. This does not yet select a parameter uniformly over all points.
-/

@[expose] public section

open MvPowerSeries
open scoped BigOperators

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {σ K J : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The same formal tests used in the projective threshold condition, for a family of local
power series. The Jacobian determinant and nonzero-weight restrictions are retained. -/
def FormalSeriesThresholdCondition (φ : J → MvPowerSeries σ K) (h : ℕ) : Prop :=
  ∀ (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K),
    (∀ i, ψ (X i) ≠ 0) → (powerSeriesJacobian ψ).det ≠ 0 → ∀ w : σ → ℕ, w ≠ 0 →
      ∃ j, (ψ (φ j)).weightedOrder w < (h : ℕ∞) *
        (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w)

/-- An ordinary order below h suffices for the complete formal-test threshold condition,
in any number of variables. -/
theorem formalSeriesThresholdCondition_of_exists_order_lt [CharZero K]
    (φ : J → MvPowerSeries σ K) (h : ℕ) (hφ : ∃ j, (φ j).order < (h : ℕ∞)) :
    FormalSeriesThresholdCondition φ h := by
  intro ψ _ hdet w hw
  obtain ⟨j, hj⟩ := hφ
  have hne : φ j ≠ 0 := fun h0 => by simp only [h0, order_zero, not_top_lt] at hj
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hj)
  have hm_lt : m < h := by rw [← hm] at hj; exact_mod_cast hj
  have hdfin : (powerSeriesJacobian ψ).det.weightedOrder w ≠ ⊤ := by
    simpa only [ne_eq, weightedOrder_eq_top_iff] using hdet
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hdfin
  have hsum : 0 < ∑ i, w i := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero hi)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hA : (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) =
      ((∑ i, w i) + d : ℕ) := by rw [← hd, Nat.cast_add]
  refine ⟨j, lt_of_le_of_lt
    (weightedOrder_algHom_le_logDiscrepancy_mul_order_of_algHom w ψ hne) ?_⟩
  rw [hA, ← hm]
  have hlt : ((∑ i, w i) + d) * m < h * ((∑ i, w i) + d) := by
    have hp : 0 < (∑ i, w i) + d := by omega
    nlinarith [Nat.mul_lt_mul_of_pos_left hm_lt hp]
  exact_mod_cast hlt

/-- With one variable the identity formal test proves necessity of the ordinary order bound.
Thus every formal test, including ramified maps, is accounted for by the order criterion. -/
theorem formalSeriesThresholdCondition_iff_exists_order_lt [CharZero K]
    (hσ : Fintype.card σ = 1) (φ : J → MvPowerSeries σ K) (h : ℕ) :
    FormalSeriesThresholdCondition φ h ↔ ∃ j, (φ j).order < (h : ℕ∞) := by
  constructor
  · intro hc
    have hw : (fun _ : σ => (1 : ℕ)) ≠ 0 := by
      intro heq
      have hsum := congrArg (fun w : σ → ℕ => ∑ i, w i) heq
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Pi.zero_apply,
        hσ] at hsum
      omega
    have hX : ∀ i, (AlgHom.id K (MvPowerSeries σ K)) (X i) ≠ 0 := by
      intro i hi
      have hci := congrArg (coeff (Finsupp.single i 1)) hi
      rw [AlgHom.id_apply, coeff_index_single_self_X, map_zero] at hci
      exact one_ne_zero hci
    obtain ⟨j, hj⟩ := hc (AlgHom.id K (MvPowerSeries σ K)) hX
      (by rw [powerSeriesJacobian_id, Matrix.det_one]; exact one_ne_zero) (fun _ => 1) hw
    refine ⟨j, ?_⟩
    simpa only [AlgHom.id_apply, powerSeriesJacobian_id, Matrix.det_one, weightedOrder_one,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hσ, Nat.cast_one,
      add_zero, mul_one, MvPowerSeries.order] using hj
  · exact formalSeriesThresholdCondition_of_exists_order_lt φ h

/-- On the projective line, the original all-point, all-formal-test condition for binary forms
is precisely the ordinary chart-order criterion at every point. -/
theorem projectiveThresholdCondition_binary_iff [CharZero K] [DecidableEq K]
    (g : J → MvPolynomial (Fin 2) K) (h : ℕ) :
    ProjectiveThresholdCondition g h ↔ ∀ (k : Fin 2)
      (p : {i : Fin 2 // i ≠ k} → K), ∃ j, (chartShiftedForm k p (g j)).order < (h : ℕ∞) := by
  have hcard (k : Fin 2) : Fintype.card {i : Fin 2 // i ≠ k} = 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  change (∀ (k : Fin 2) (p : {i : Fin 2 // i ≠ k} → K),
    FormalSeriesThresholdCondition (fun j => chartShiftedForm k p (g j)) h) ↔ _
  exact forall_congr' fun k => forall_congr' fun p =>
    formalSeriesThresholdCondition_iff_exists_order_lt (hcard k) _ h

end MixedFujita
