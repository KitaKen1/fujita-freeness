/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MinimizationIntervalArithmetic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The limit argument of the specialization comparison (6) in §2.3. The functional depends on a test
valuation and a basis only through the discrepancy a = A(v) and the normalized values
q_i = v(s_i)/A(v): F = (1/N) Σ exp(a/t - a q_i/j), and a can be any positive number after
scaling. Let R_z be the set of profiles realized at z with v(s_i)/A(v) ≥ q_i, a downward closed
set, and f(z) the infimum of F over a > 0 and q ∈ R_z. If every rational profile realized at y is
realized at x, then f(y) ≥ f(x): approximate a real profile q ∈ R_y from below by a rational
profile q' ≤ q, which is realized at y, hence at x, and F(a, q') ≤ e^(aδ/j) F(a, q). The choice of
the very general point y, which needs the closedness of the realization sets (Lemma 3), is an
input; the attainment of the minimum is not used.
-/

@[expose] public section

namespace MixedFujita

/-- The values of the functional over the profiles in R. -/
def profileValueSet {N : ℕ} (j : ℕ) (t : ℝ) (R : Set (Fin N → ℝ)) : Set ℝ :=
  {F | ∃ a : ℝ, 0 < a ∧ ∃ q ∈ R, F = minimizationFunctional j t a (fun i => a * q i)}

theorem minimizationFunctional_nonneg {N : ℕ} (j : ℕ) (t A : ℝ) (vals : Fin N → ℝ) :
    0 ≤ minimizationFunctional j t A vals :=
  div_nonneg (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le) (Nat.cast_nonneg N)

/-- Lowering the profile by less than δ raises the functional by at most the factor e^(aδ/j). -/
theorem minimizationFunctional_le_of_lower {N : ℕ} {j : ℕ} (hj : 0 < j) (t : ℝ) {a δ : ℝ}
    (ha : 0 ≤ a) {q q' : Fin N → ℝ} (hq' : ∀ i, q i - δ < q' i) :
    minimizationFunctional j t a (fun i => a * q' i) ≤
      Real.exp (a * δ / j) * minimizationFunctional j t a (fun i => a * q i) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  unfold minimizationFunctional
  rw [mul_div_assoc', Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : a * (q i - δ) ≤ a * q' i := mul_le_mul_of_nonneg_left (hq' i).le ha
  have h2 : a * (q i - δ) / j ≤ a * q' i / j := div_le_div_of_nonneg_right h1 hj'.le
  have h3 : a * (q i - δ) / j = a * q i / j - a * δ / j := by ring
  linarith

/-- §2.3 (6), approximation step: a real profile realized at y is approached, in the value of the
functional, by rational profiles realized at x. -/
theorem specialization_approximation {N : ℕ} {j : ℕ} (hj : 0 < j) (t : ℝ)
    (Ry Rx : Set (Fin N → ℝ)) (hdown : ∀ q ∈ Ry, ∀ q', q' ≤ q → q' ∈ Ry)
    (hrat : ∀ q : Fin N → ℚ, (fun i => (q i : ℝ)) ∈ Ry → (fun i => (q i : ℝ)) ∈ Rx)
    {a : ℝ} (ha : 0 < a) {q : Fin N → ℝ} (hq : q ∈ Ry) {ε : ℝ} (hε : 0 < ε) :
    ∃ q' ∈ Rx, minimizationFunctional j t a (fun i => a * q' i) ≤
      minimizationFunctional j t a (fun i => a * q i) + ε := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  set F := minimizationFunctional j t a (fun i => a * q i) with hF
  have hF0 : 0 ≤ F := minimizationFunctional_nonneg _ _ _ _
  set δ : ℝ := j * Real.log (1 + ε / (F + 1)) / a with hδ
  have hlog : 0 < Real.log (1 + ε / (F + 1)) :=
    Real.log_pos (by have : 0 < ε / (F + 1) := div_pos hε (by linarith); linarith)
  have hδ0 : 0 < δ := div_pos (mul_pos hj' hlog) ha
  have hrq : ∀ i, ∃ r : ℚ, q i - δ < r ∧ (r : ℝ) < q i := fun i =>
    exists_rat_btwn (by linarith)
  choose r hr using hrq
  set q' : Fin N → ℝ := fun i => (r i : ℝ) with hq'
  have hle : q' ≤ q := fun i => (hr i).2.le
  have hmem : q' ∈ Rx := hrat r (hdown q hq q' hle)
  refine ⟨q', hmem, ?_⟩
  have hbound := minimizationFunctional_le_of_lower hj t ha.le (q := q) (q' := q')
    (fun i => (hr i).1)
  have hexp : Real.exp (a * δ / j) = 1 + ε / (F + 1) := by
    have : a * δ / j = Real.log (1 + ε / (F + 1)) := by
      rw [hδ]
      field_simp
    rw [this, Real.exp_log (by have : 0 < ε / (F + 1) := div_pos hε (by linarith); linarith)]
  rw [hexp] at hbound
  have hfrac : ε / (F + 1) * F ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc minimizationFunctional j t a (fun i => a * q' i) ≤ (1 + ε / (F + 1)) * F := hbound
    _ = F + ε / (F + 1) * F := by ring
    _ ≤ F + ε := by linarith

/-- §2.3 (6): if every rational profile realized at y is realized at x, then f(y) ≥ f(x). -/
theorem specialization_comparison {N : ℕ} {j : ℕ} (hj : 0 < j) (t : ℝ)
    (Ry Rx : Set (Fin N → ℝ)) (hdown : ∀ q ∈ Ry, ∀ q', q' ≤ q → q' ∈ Ry)
    (hrat : ∀ q : Fin N → ℚ, (fun i => (q i : ℝ)) ∈ Ry → (fun i => (q i : ℝ)) ∈ Rx)
    (hne : Ry.Nonempty) :
    sInf (profileValueSet j t Rx) ≤ sInf (profileValueSet j t Ry) := by
  obtain ⟨q₀, hq₀⟩ := hne
  have hneY : (profileValueSet j t Ry).Nonempty := ⟨_, 1, one_pos, q₀, hq₀, rfl⟩
  have hbddX : BddBelow (profileValueSet j t Rx) := by
    refine ⟨0, ?_⟩
    rintro F ⟨a, -, q, -, rfl⟩
    exact minimizationFunctional_nonneg _ _ _ _
  apply le_csInf hneY
  rintro F ⟨a, ha, q, hq, rfl⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨q', hq', hle⟩ := specialization_approximation hj t Ry Rx hdown hrat ha hq hε
  exact (csInf_le hbddX ⟨a, ha, q', hq', rfl⟩).trans hle

/-- §5.1: the minimizing pair has F(v, s) = f(x) ≤ f(y) ≤ F(v_ε, s) for the perturbed valuations
v_ε centred at y, so ε ↦ F(v_ε, s) has a right minimum at 0, the input of (16). -/
theorem right_minimum_of_specialization {F : ℝ → ℝ} {fx fy : ℝ} (h0 : F 0 = fx)
    (hxy : fx ≤ fy) (hy : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), fy ≤ F ε) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), F 0 ≤ F ε := by
  filter_upwards [hy] with ε hε
  rw [h0]
  exact hxy.trans hε

end MixedFujita
