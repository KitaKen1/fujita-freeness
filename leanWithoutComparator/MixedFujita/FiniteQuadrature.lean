/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictGap
public import Mathlib.Tactic.NormNum

/-!
An explicit finite alternative to the second Riemann-sum limit in Section 4.
The polynomial lower envelope of the exponential has quadrature error at
most (1+c)/l. Thus a single sufficiently large finite partition preserves
the strict gap. This does not establish the degree-limit inputs.
-/

@[expose] public section

namespace MixedFujita

open MeasureTheory

noncomputable def uniformGridSum (f : ℝ → ℝ) (l : ℕ) : ℝ :=
  (∑ i ∈ Finset.range l, f ((i : ℝ) / l)) / l

/-- Exact Darboux bounds, with the endpoint difference as the error. -/
theorem uniformGridSum_integral_bounds (f : ℝ → ℝ) (l : ℕ) (hl : 0 < l)
    (hf : Continuous f) (hmono : MonotoneOn f (Set.Icc 0 1)) :
    uniformGridSum f l ≤ (∫ s in (0 : ℝ)..1, f s) ∧
      (∫ s in (0 : ℝ)..1, f s) ≤ uniformGridSum f l + (f 1 - f 0) / l := by
  have hlr : 0 < (l : ℝ) := by exact_mod_cast hl
  let a : ℕ → ℝ := fun i => (i : ℝ) / l
  have ha0 : a 0 = 0 := by simp [a]
  have hal : a l = 1 := by simp [a, hl.ne']
  have hstep (i : ℕ) : a (i + 1) - a i = 1 / l := by dsimp [a]; push_cast; ring
  have hab (i : ℕ) : a i ≤ a (i + 1) := by
    have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hlr.le
    rw [← hstep i] at h
    linarith
  have hmem (i : ℕ) (hi : i ≤ l) : a i ∈ Set.Icc 0 1 := by
    constructor
    · dsimp [a]; positivity
    · dsimp [a]
      apply (div_le_one hlr).mpr
      exact_mod_cast hi
  have hlo (i : ℕ) (hi : i < l) :
      f (a i) / l ≤ ∫ s in a i..a (i + 1), f s := by
    have h := intervalIntegral.integral_mono_on (hab i)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f (a i)) volume
        (a i) (a (i + 1))) (hf.intervalIntegrable _ _)
      (fun s hs => hmono (hmem i hi.le)
        ⟨(hmem i hi.le).1.trans hs.1, hs.2.trans (hmem (i + 1) (by omega)).2⟩ hs.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep, one_div_mul_eq_div] using h
  have hhi (i : ℕ) (hi : i < l) :
      (∫ s in a i..a (i + 1), f s) ≤ f (a (i + 1)) / l := by
    have h := intervalIntegral.integral_mono_on (hab i) (hf.intervalIntegrable _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f (a (i + 1))) volume
        (a i) (a (i + 1)))
      (fun s hs => hmono
        ⟨(hmem i hi.le).1.trans hs.1, hs.2.trans (hmem (i + 1) (by omega)).2⟩
        (hmem (i + 1) (by omega)) hs.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, hstep, one_div_mul_eq_div] using h
  have hint : (∑ i ∈ Finset.range l, ∫ s in a i..a (i + 1), f s) =
      ∫ s in (0 : ℝ)..1, f s := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (n := l) (f := f) (μ := volume) (fun _ _ => hf.intervalIntegrable _ _)
    simpa only [ha0, hal] using h
  have hlow := Finset.sum_le_sum (s := Finset.range l)
    (fun i hi => hlo i (Finset.mem_range.mp hi))
  have hupp := Finset.sum_le_sum (s := Finset.range l)
    (fun i hi => hhi i (Finset.mem_range.mp hi))
  rw [hint, ← Finset.sum_div] at hlow
  rw [hint, ← Finset.sum_div] at hupp
  have hend : (∑ i ∈ Finset.range l, f (a (i + 1))) -
      (∑ i ∈ Finset.range l, f (a i)) = f 1 - f 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => f (a i))]
    rw [ha0, hal]
  refine ⟨hlow, ?_⟩
  have heq : (∑ i ∈ Finset.range l, f (a (i + 1))) / l =
      uniformGridSum f l + (f 1 - f 0) / l := by
    unfold uniformGridSum
    change _ = (∑ i ∈ Finset.range l, f (a i)) / l + _
    rw [← add_div]
    congr 1
    linarith
  rwa [heq] at hupp

/-- Power sums have an explicit error bound; no Bernoulli numbers are needed. -/
theorem uniformGridSum_power_bounds (n l : ℕ) (hl : 0 < l) :
    1 / (n + 1 : ℝ) - 1 / l ≤ uniformGridSum (fun s => s ^ n) l ∧
      uniformGridSum (fun s => s ^ n) l ≤ 1 / (n + 1 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := uniformGridSum_integral_bounds (fun s : ℝ => s ^ n) l hl
    (continuous_id.pow n) (fun x hx _ _ hxy => pow_le_pow_left₀ hx.1 hxy n)
  rw [integral_pow] at hlo hhi
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero] at hlo hhi
  have hzero : (0 : ℝ) ≤ (0 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have hlr : (0 : ℝ) ≤ l := by positivity
  have he : (1 - (0 : ℝ) ^ n) / l ≤ 1 / l :=
    div_le_div_of_nonneg_right (by linarith) hlr
  exact ⟨by linarith, hlo⟩

/-- The exponential lower envelope is a linear combination of two powers. -/
theorem uniformGridSum_linear_weight (n l : ℕ) (c : ℝ) :
    uniformGridSum (fun s => s ^ n * (1 + (1 - s) * c)) l =
      (1 + c) * uniformGridSum (fun s => s ^ n) l -
        c * uniformGridSum (fun s => s ^ (n + 1)) l := by
  unfold uniformGridSum
  rw [← mul_div_assoc, ← mul_div_assoc, ← sub_div, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [pow_succ]
  ring

/-- Explicit replacement for taking l→∞ in the lower envelope. -/
theorem uniformGridSum_linear_weight_lower_bound (n l : ℕ) (hl : 0 < l)
    {c : ℝ} (hc : 0 ≤ c) :
    1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ)) - (1 + c) / l ≤
      uniformGridSum (fun s => s ^ n * (1 + (1 - s) * c)) l := by
  obtain ⟨hnlo, _⟩ := uniformGridSum_power_bounds n l hl
  obtain ⟨_, hnhi⟩ := uniformGridSum_power_bounds (n + 1) l hl
  have h1 := mul_le_mul_of_nonneg_left hnlo (by linarith : 0 ≤ 1 + c)
  have h2 := mul_le_mul_of_nonneg_left hnhi hc
  rw [uniformGridSum_linear_weight]
  have heq : (1 + c) * (1 / (n + 1 : ℝ) - 1 / l) -
      c * (1 / (n + 1 + 1 : ℝ)) =
      1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ)) - (1 + c) / l := by
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← heq]
  push_cast at h2
  linarith

theorem uniformGridSum_exponential_ge_linear (n l : ℕ) (c : ℝ) :
    uniformGridSum (fun s => s ^ n * (1 + (1 - s) * c)) l ≤
      uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * c)) l := by
  unfold uniformGridSum
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) n)
  simpa only [add_comm] using Real.add_one_le_exp ((1 - (i : ℝ) / l) * c)

/-- In positive ambient dimension the zero endpoint contributes nothing. -/
theorem exponential_uniformGridSum_eq_interior (n l : ℕ) (hn : 0 < n)
    (hl : 1 ≤ l) (c : ℝ) :
    uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * c)) l =
      (∑ i ∈ Finset.Ico 1 l, ((i : ℝ) / l) ^ n * Real.exp ((1 - (i : ℝ) / l) * c)) / l := by
  rw [Finset.sum_Ico_eq_sub _ hl]
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_div, zero_pow hn.ne', zero_mul,
    sub_zero, uniformGridSum]

/-- A single finite partition preserves any strict gap below the known integral.
Its size is chosen above max(1, lam*(1+c)/(lam*I-u)). -/
theorem exists_finite_exponential_grid_gap (n : ℕ) {c lam u : ℝ}
    (hc : 0 ≤ c) (hlam : 0 < lam)
    (hgap : u < lam * (1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ)))) :
    ∃ l : ℕ, 2 ≤ l ∧ u < lam *
      uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * c)) l := by
  let I : ℝ := 1 / (n + 1 : ℝ) + c / ((n + 1 : ℝ) * (n + 2 : ℝ))
  have hmargin : 0 < lam * I - u := sub_pos.mpr hgap
  obtain ⟨l, hl⟩ := exists_nat_gt (max 1 (lam * (1 + c) / (lam * I - u)))
  have hl1 : (1 : ℝ) < l := (le_max_left _ _).trans_lt hl
  have hl2 : 2 ≤ l := by exact_mod_cast hl1
  have hlr : 0 < (l : ℝ) := by linarith
  have herr : lam * (1 + c) / l < lam * I - u := by
    have h := (le_max_right _ _).trans_lt hl
    have hm := (div_lt_iff₀ hmargin).mp h
    exact (div_lt_iff₀ hlr).mpr (by nlinarith)
  have hpoly := mul_le_mul_of_nonneg_left
    (uniformGridSum_linear_weight_lower_bound n l (by omega) hc) hlam.le
  have hexp := mul_le_mul_of_nonneg_left
    (uniformGridSum_exponential_ge_linear n l c) hlam.le
  refine ⟨l, hl2, ?_⟩
  have hs : u < lam * (I - (1 + c) / l) := by
    rw [mul_sub, ← mul_div_assoc]
    linarith
  exact hs.trans_le (hpoly.trans hexp)

/-- The manuscript's t and one finite partition suffice for the second limit. -/
theorem exists_parameter_finite_partition_gap (n : ℕ) {a b lam t₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hlam : lam * b = n + 1) (ht₀ : t₀ < b) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ l : ℕ, 2 ≤ l ∧
      1 / t < lam * uniformGridSum
        (fun s => s ^ n * Real.exp ((1 - s) * (a / b))) l := by
  have hβ : 0 < a / (b * (n + 2 : ℝ)) := by positivity
  obtain ⟨t, ht₀', ht, htb, hgap⟩ := exists_parameter_with_gap hb hβ ht₀
  have hlameq : lam = (n + 1 : ℝ) / b := (eq_div_iff hb.ne').mpr hlam
  have hlampos : 0 < lam := by rw [hlameq]; positivity
  have heq : lam * (1 / (n + 1 : ℝ) + (a / b) / ((n + 1 : ℝ) * (n + 2 : ℝ))) =
      (1 + a / (b * (n + 2 : ℝ))) / b := by
    rw [hlameq]
    have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
    have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
    field_simp
  obtain ⟨l, hl, hgrid⟩ := exists_finite_exponential_grid_gap n
    (by positivity : 0 ≤ a / b) hlampos (by rwa [heq])
  exact ⟨t, ht₀', ht, htb, l, hl, hgrid⟩

end MixedFujita
