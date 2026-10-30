/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
The arithmetic of §3.1 of the manuscript. A basis of an N-dimensional space has at least dim U
vectors outside any subspace W with U ⊓ W = 0, since the basis vectors inside W are independent
in W and dim U + dim W ≤ N. The functional F = (1/N) Σ_i exp(A/t - v_i/j) is at least
κ exp(A/(2t)) when at least κ N of the values satisfy v_i ≤ j A/(2t), and at least
exp(A/t - C A) when every v_i ≤ C j A. If F ≤ 1 - δ/2 these two bounds confine A to the interval
-log(1 - δ/2)/C ≤ A ≤ 2 b log(1/κ) for t ≤ b, the bound (10).
-/

@[expose] public section

open Finset

namespace MixedFujita

open Classical in
/-- A basis has at least dim U vectors outside a subspace W with U ⊓ W = 0. -/
theorem basis_card_not_mem_ge {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (U W : Submodule K V)
    (hUW : U ⊓ W = ⊥) :
    Module.finrank K U ≤ (univ.filter (fun i => b i ∉ W)).card := by
  have h1 : (univ.filter (fun i => b i ∈ W)).card ≤ Module.finrank K W := by
    have hind : LinearIndependent K (fun i : (univ.filter (fun i => b i ∈ W) : Finset (Fin N)) =>
        (⟨b i, (mem_filter.mp i.2).2⟩ : W)) := by
      apply LinearIndependent.of_comp W.subtype
      exact b.linearIndependent.comp (fun i : (univ.filter (fun i => b i ∈ W) : Finset (Fin N)) =>
        (i : Fin N)) Subtype.val_injective
    have h := hind.fintype_card_le_finrank
    rwa [Fintype.card_coe] at h
  have h2 : Module.finrank K U + Module.finrank K W ≤ N := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U W
    rw [hUW, finrank_bot, add_zero] at h
    have h3 := Submodule.finrank_le (U ⊔ W)
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin] at h3
    omega
  have h4 := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun i => b i ∈ W)
  rw [card_univ, Fintype.card_fin] at h4
  omega

/-- The same count, as a finite set of indices. -/
theorem basis_exists_card_not_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {N : ℕ} (b : Module.Basis (Fin N) K V) (U W : Submodule K V)
    (hUW : U ⊓ W = ⊥) :
    ∃ S : Finset (Fin N), Module.finrank K U ≤ S.card ∧ ∀ i ∈ S, b i ∉ W := by
  classical
  exact ⟨univ.filter (fun i => b i ∉ W), basis_card_not_mem_ge b U W hUW,
    fun i hi => (mem_filter.mp hi).2⟩

/-- The functional of §2.3: (1/N) Σ_i exp(A/t - v_i/j). -/
noncomputable def minimizationFunctional {N : ℕ} (j : ℕ) (t A : ℝ) (vals : Fin N → ℝ) : ℝ :=
  (∑ i, Real.exp (A / t - vals i / j)) / N

/-- If at least κ N of the values are at most c, then F ≥ κ exp(A/t - c/j). -/
theorem minimizationFunctional_ge_of_count {N : ℕ} (hN : 0 < N) (j : ℕ) {t A κ c : ℝ}
    (vals : Fin N → ℝ)
    (hcount : κ * N ≤ ((univ.filter (fun i => vals i ≤ c)).card : ℝ)) :
    κ * Real.exp (A / t - c / j) ≤ minimizationFunctional j t A vals := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set S := univ.filter (fun i => vals i ≤ c) with hS
  have hterm : ∀ i ∈ S, Real.exp (A / t - c / j) ≤ Real.exp (A / t - vals i / j) := by
    intro i hi
    apply Real.exp_le_exp.mpr
    have hv := (mem_filter.mp hi).2
    have : vals i / j ≤ c / j := div_le_div_of_nonneg_right hv (Nat.cast_nonneg j)
    linarith
  have hsum : (S.card : ℝ) * Real.exp (A / t - c / j) ≤ ∑ i, Real.exp (A / t - vals i / j) := by
    calc (S.card : ℝ) * Real.exp (A / t - c / j) = ∑ _i ∈ S, Real.exp (A / t - c / j) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, Real.exp (A / t - vals i / j) := sum_le_sum hterm
      _ ≤ ∑ i, Real.exp (A / t - vals i / j) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun i _ _ => (Real.exp_pos _).le)
  have hE := Real.exp_pos (A / t - c / j)
  unfold minimizationFunctional
  rw [le_div_iff₀ hNpos]
  nlinarith [mul_le_mul_of_nonneg_right hcount hE.le]

/-- If every value is at most c, then F ≥ exp(A/t - c/j). -/
theorem minimizationFunctional_ge_of_all {N : ℕ} (hN : 0 < N) (j : ℕ) {t A c : ℝ}
    (vals : Fin N → ℝ) (hall : ∀ i, vals i ≤ c) :
    Real.exp (A / t - c / j) ≤ minimizationFunctional j t A vals := by
  have h := minimizationFunctional_ge_of_count hN j (t := t) (A := A) (κ := 1) (c := c) vals (by
    rw [one_mul]
    have : univ.filter (fun i => vals i ≤ c) = univ := filter_true_of_mem fun i _ => hall i
    rw [this, card_univ, Fintype.card_fin])
  rwa [one_mul] at h

/-- The bound (10): F ≤ 1 - δ/2 confines A to [-log(1 - δ/2)/C, 2 b log(1/κ)]. -/
theorem logDiscrepancy_bounds_of_functional {κ b C δ A t F : ℝ} (hκ : 0 < κ) (hC : 0 < C)
    (hδ : 0 < δ) (hδ2 : δ < 2) (hA : 0 ≤ A) (ht : 0 < t) (htb : t ≤ b)
    (h8 : κ * Real.exp (A / (2 * t)) ≤ F) (h9 : Real.exp (A / t - C * A) ≤ F)
    (hF : F ≤ 1 - δ / 2) :
    -Real.log (1 - δ / 2) / C ≤ A ∧ A ≤ 2 * b * Real.log (1 / κ) := by
  have hpos : (0 : ℝ) < 1 - δ / 2 := by linarith
  constructor
  · have h := (Real.le_log_iff_exp_le hpos).mpr (h9.trans hF)
    have hAt : 0 ≤ A / t := div_nonneg hA ht.le
    rw [div_le_iff₀ hC]
    linarith
  · have hlt : κ * Real.exp (A / (2 * t)) < 1 := lt_of_le_of_lt (h8.trans hF) (by linarith)
    have hexp : Real.exp (A / (2 * t)) < 1 / κ := by
      rw [lt_div_iff₀ hκ]
      linarith
    have hlog := (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 1 / κ)).mpr hexp
    have h2t : (0 : ℝ) < 2 * t := by positivity
    have hA2 : A < 2 * t * Real.log (1 / κ) := by
      rw [div_lt_iff₀ h2t] at hlog
      linarith
    have hlog0 : 0 ≤ Real.log (1 / κ) := by
      have : 0 ≤ A / (2 * t) := div_nonneg hA h2t.le
      linarith
    nlinarith

end MixedFujita
