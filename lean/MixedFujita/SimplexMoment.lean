/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictGap
public import MixedFujita.GradedSlices
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Choose.Bounds
public import Lean.Elab.Tactic.Omega

/-! A one-dimensional counting proof of the finite simplex moment bound.
It avoids a general rearrangement theorem and high-dimensional integration. -/

@[expose] public section

namespace MixedFujita

open MeasureTheory

/-- Stars and bars, with a slack coordinate. No ordering of E is required. -/
theorem lattice_cost_count_bound (n m : ℕ) (E : Finset (Fin n → ℕ)) :
    (E.filter (fun γ => (∑ i, γ i) + n ≤ m)).card ≤ m.choose n := by
  classical
  by_cases hnm : n ≤ m
  · let S := E.filter (fun γ => (∑ i, γ i) + n ≤ m)
    let f : S → Sym (Fin (n + 1)) (m - n) := fun γ =>
      (Sym.equivNatSumOfFintype (Fin (n + 1)) (m - n)).symm
        ⟨Fin.cons (m - n - ∑ i, γ.val i) γ.val, by
          have hγ := (Finset.mem_filter.mp γ.property).2
          simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
          omega⟩
    have hf : Function.Injective f := by
      intro γ δ h
      have hfun := congrArg Subtype.val
        ((Sym.equivNatSumOfFintype (Fin (n + 1)) (m - n)).symm.injective h)
      apply Subtype.ext
      funext i
      exact congrFun hfun i.succ
    have hcard : Fintype.card (Sym (Fin (n + 1)) (m - n)) = m.choose n := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin]
      have hm : n + 1 + (m - n) - 1 = m := by omega
      rw [hm, ← Nat.choose_symm (Nat.sub_le m n)]
      congr 1
      omega
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_coe, hcard] using h
  · have hempty : E.filter (fun γ => (∑ i, γ i) + n ≤ m) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      have h := (Finset.mem_filter.mp hγ).2
      omega
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

noncomputable def cumulativeCount {ι : Type*} (E : Finset ι) (c : ι → ℝ)
    (t : ℝ) : ℝ := by
  classical
  exact ((E.filter (fun i => c i < t)).card : ℝ)

theorem cumulativeCount_eq_sum {ι : Type*} (E : Finset ι) (c : ι → ℝ) (t : ℝ) :
    cumulativeCount E c t = ∑ i ∈ E, if c i < t then (1 : ℝ) else 0 := by
  classical
  exact Finset.natCast_card_filter _ _

theorem step_intervalIntegrable {c R : ℝ} :
    IntervalIntegrable (fun t : ℝ => if c < t then (1 : ℝ) else 0) volume 0 R := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 R :=
    continuous_const.intervalIntegrable 0 R
  have hi : IntervalIntegrable (Set.Iic c |>.indicator (fun _ : ℝ => (1 : ℝ)))
      volume 0 R :=
    intervalIntegrable_iff.mpr (hconst.def'.indicator measurableSet_Iic)
  have heq : (fun t : ℝ => if c < t then (1 : ℝ) else 0) =
      (fun t => 1 - (Set.Iic c).indicator (fun _ : ℝ => (1 : ℝ)) t) := by
    funext t
    by_cases h : c < t
    · simp [h, Set.indicator_of_notMem, not_le.mpr h]
    · simp [h, Set.indicator_of_mem, le_of_not_gt h]
  rw [heq]
  exact hconst.sub hi

theorem integral_step {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, if c < t then (1 : ℝ) else 0) = max 0 (R - c) := by
  by_cases hcR : c ≤ R
  · have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 R :=
      continuous_const.intervalIntegrable 0 R
    have hi : IntervalIntegrable (Set.Iic c |>.indicator (fun _ : ℝ => (1 : ℝ)))
        volume 0 R :=
      intervalIntegrable_iff.mpr (hconst.def'.indicator measurableSet_Iic)
    have heq : (fun t : ℝ => if c < t then (1 : ℝ) else 0) =
        (fun t => 1 - (Set.Iic c).indicator (fun _ : ℝ => (1 : ℝ)) t) := by
      funext t
      by_cases h : c < t
      · simp [h, Set.indicator_of_notMem, not_le.mpr h]
      · simp [h, Set.indicator_of_mem, le_of_not_gt h]
    rw [heq, intervalIntegral.integral_sub hconst hi]
    have hI : Set.Iic c = {x : ℝ | x ≤ c} := Set.ext (fun _ => Iff.rfl)
    rw [hI, intervalIntegral.integral_indicator (show c ∈ Set.Icc 0 R from ⟨hc, hcR⟩)]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    exact (max_eq_right (sub_nonneg.mpr hcR)).symm
  · have heq : (∫ t in (0 : ℝ)..R, if c < t then (1 : ℝ) else 0) =
        ∫ _ in (0 : ℝ)..R, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htR : t ≤ R := (Set.uIcc_of_le hR ▸ ht).2
      simp [not_lt.mpr (htR.trans (le_of_not_ge hcR))]
    rw [heq, intervalIntegral.integral_zero, max_eq_left]
    linarith

theorem cumulativeCount_intervalIntegrable {ι : Type*} (E : Finset ι) (c : ι → ℝ) (R : ℝ) :
    IntervalIntegrable (cumulativeCount E c) volume 0 R := by
  simp only [funext (cumulativeCount_eq_sum E c)]
  simpa only [Finset.sum_fn] using
    IntervalIntegrable.sum E (fun i _ => (step_intervalIntegrable (c := c i) (R := R)))

theorem integral_cumulativeCount {ι : Type*} (E : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ E, 0 ≤ c i) {R : ℝ} (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R, cumulativeCount E c t) = ∑ i ∈ E, max 0 (R - c i) := by
  simp_rw [cumulativeCount_eq_sum]
  rw [intervalIntegral.integral_finsetSum (fun _ _ => step_intervalIntegrable)]
  exact Finset.sum_congr rfl (fun i hi => integral_step (hc i hi) hR)

theorem finite_moment_lower_bound_of_count {ι : Type*}
    (E : Finset ι) (c : ι → ℝ) (n : ℕ) (hc : ∀ i ∈ E, 0 ≤ c i)
    (hcount : ∀ t ≥ 0, cumulativeCount E c t ≤ t ^ n / (n.factorial : ℝ))
    {R : ℝ} (hR : 0 ≤ R) :
    R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) ≤
      ∑ i ∈ E, c i := by
  have hsum : R * (E.card : ℝ) - ∑ i ∈ E, c i ≤
      ∫ t in (0 : ℝ)..R, cumulativeCount E c t := by
    rw [integral_cumulativeCount E c hc hR]
    calc
      _ = ∑ i ∈ E, (R - c i) := by
        rw [Finset.sum_sub_distrib]
        simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => le_max_right _ _)
  have hupper := intervalIntegral.integral_mono_on hR
    (cumulativeCount_intervalIntegrable E c R)
    ((continuous_id.pow n).div_const (n.factorial : ℝ) |>.intervalIntegrable 0 R)
    (fun t ht => hcount t ht.1)
  have hpoly : (∫ t in (0 : ℝ)..R, t ^ n / (n.factorial : ℝ)) =
      R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    rw [div_div]
  change (∫ t in (0 : ℝ)..R, cumulativeCount E c t) ≤
    (∫ t in (0 : ℝ)..R, t ^ n / (n.factorial : ℝ)) at hupper
  rw [hpoly] at hupper
  linarith

theorem lattice_cumulativeCount_bound (n : ℕ) (E : Finset (Fin n → ℕ))
    {t : ℝ} (ht : 0 ≤ t) :
    cumulativeCount E (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ)) t ≤
      t ^ n / (n.factorial : ℝ) := by
  classical
  have hsubset : E.filter (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ) < t) ⊆
      E.filter (fun γ => (∑ i, γ i) + n ≤ ⌊t⌋₊) := by
    intro γ hγ
    obtain ⟨hE, hγ⟩ := Finset.mem_filter.mp hγ
    exact Finset.mem_filter.mpr ⟨hE, (Nat.le_floor_iff ht).mpr hγ.le⟩
  calc
    _ ≤ ((E.filter (fun γ => (∑ i, γ i) + n ≤ ⌊t⌋₊)).card : ℝ) := by
      unfold cumulativeCount
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (⌊t⌋₊.choose n : ℝ) := by exact_mod_cast lattice_cost_count_bound n ⌊t⌋₊ E
    _ ≤ (⌊t⌋₊ : ℝ) ^ n / (n.factorial : ℝ) := Nat.choose_le_pow_div n ⌊t⌋₊
    _ ≤ _ := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le ht) n) (by positivity)

/-- The exact finite bound used in Section 4. The optimum radius is provided
explicitly, so no minimizer or rearrangement API is needed. -/
theorem simplex_moment_lower_bound (n : ℕ) (hn : 0 < n) (E : Finset (Fin n → ℕ)) :
    (n : ℝ) / (n + 1 : ℝ) *
      ((((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹) ^ (n + 1)) /
        (n.factorial : ℝ) ≤
      ∑ γ ∈ E, (((∑ i, γ i) + n : ℕ) : ℝ) := by
  let R : ℝ := ((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hRn : R ^ n = (n.factorial : ℝ) * (E.card : ℝ) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ hn', Real.rpow_one]
  have hpower : R ^ (n + 1) = R * (n.factorial : ℝ) * (E.card : ℝ) := by
    rw [pow_succ, hRn]
    ring
  have hg := finite_moment_lower_bound_of_count E
    (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ)) n
    (fun _ _ => by positivity) (fun _ ht => lattice_cumulativeCount_bound n E ht) hR
  calc
    _ = R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
      change (n : ℝ) / (n + 1 : ℝ) * R ^ (n + 1) / (n.factorial : ℝ) = _
      rw [hpower]
      field_simp
      ring
    _ ≤ _ := hg

theorem simplex_moment_lower_bound_int (n : ℕ) (hn : 0 < n)
    (E : Finset (Fin n → ℤ)) (hE : ∀ γ ∈ E, ∀ i, 0 ≤ γ i) :
    (n : ℝ) / (n + 1 : ℝ) *
      ((((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹) ^ (n + 1)) /
        (n.factorial : ℝ) ≤
      ∑ γ ∈ E, ((∑ i, (γ i : ℝ)) + (n : ℝ)) := by
  classical
  let f : (Fin n → ℤ) → (Fin n → ℕ) := fun γ i => (γ i).toNat
  have hf : Set.InjOn f E := by
    intro γ hγ δ hδ heq
    funext i
    have h := congrArg (fun a : ℕ => (a : ℤ)) (congrFun heq i)
    simpa only [f, Int.toNat_of_nonneg (hE γ hγ i),
      Int.toNat_of_nonneg (hE δ hδ i)] using h
  have hg := simplex_moment_lower_bound n hn (E.image f)
  rw [Finset.card_image_of_injOn hf, Finset.sum_image hf] at hg
  refine hg.trans_eq (Finset.sum_congr rfl (fun γ hγ => ?_))
  simp only [Nat.cast_add, Nat.cast_sum, f]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact_mod_cast Int.toNat_of_nonneg (hE γ hγ i)

/-- The finite first-moment bound summed over slices. The nonnegative
exponent condition must still be supplied by the geometric Taylor data. -/
theorem weighted_exponentSlice_firstMoment_bound {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hΓ : ∀ p ∈ exponentSupport Γ j, ∀ γ ∈ exponentSlice Γ j p, ∀ i, 0 ≤ γ i) :
    (d + 1 : ℝ) / (d + 2 : ℝ) * weightedSliceMoment Γ j w ≤
      ∑ p ∈ exponentSupport Γ j,
        w p * (∑ γ ∈ exponentSlice Γ j p, ((∑ i, (γ i : ℝ)) + (d + 1 : ℝ))) := by
  calc
    _ = ∑ p ∈ exponentSupport Γ j,
        w p * ((d + 1 : ℝ) / (d + 2 : ℝ) *
          sliceRadius (exponentSlice Γ j p) ^ (d + 2) / ((d + 1).factorial : ℝ)) := by
      simp only [weightedSliceMoment, mul_div_assoc, Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hw p)
      have h := simplex_moment_lower_bound_int (d + 1) (by omega)
        (exponentSlice Γ j p) (hΓ p hp)
      simpa only [sliceRadius, Nat.cast_add, Nat.cast_one, add_assoc,
        one_add_one_eq_two, Nat.add_assoc] using h

end MixedFujita
