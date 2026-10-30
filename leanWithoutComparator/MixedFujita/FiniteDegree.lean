/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SimplexMoment
public import MixedFujita.FirstVariation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Section 4 at a fixed finite partition. Telescoping the slice growth and
comparing normalized objectives are finite inequalities. No Hilbert
asymptotic, moving-center uniformity, or geometric minimizer is assumed
to have been constructed by this module.
-/

@[expose] public section

namespace MixedFujita

/-- Accumulate all increments, including the initial nonnegative moment. -/
theorem finite_moment_growth_sum (B R : ℕ → ℝ) (k : ℕ)
    (hB : 0 ≤ B 0) (hg : ∀ i < k, B i + R i ≤ B (i + 1)) :
    (∑ i ∈ Finset.range k, R i) ≤ B k := by
  have hsum := Finset.sum_le_sum (s := Finset.range k)
    (f := R) (g := fun i => B (i + 1) - B i)
    (fun i hi => by have h := hg i (Finset.mem_range.mp hi); linarith)
  rw [Finset.sum_range_sub] at hsum
  linarith

/-- The fixed-partition inequality immediately before the degree limit. -/
theorem finite_partition_moment_bound (B Q a : ℕ → ℝ) (k : ℕ)
    {D m Qm T : ℝ} (hD : 0 ≤ D) (hm : 0 < m) (hQm : 0 < Qm)
    (hB : 0 ≤ B 0)
    (hg : ∀ i < k, B i + (D + 1) * a i * Q i ≤ B (i + 1))
    (hfirst : D / (D + 1) * B k ≤ m * Qm * (T + D / m)) :
    D * (∑ i ∈ Finset.range k, (a i / m) * (Q i / Qm)) ≤ T + D / m := by
  have hsum := finite_moment_growth_sum B (fun i => (D + 1) * a i * Q i) k hB hg
  have hfac : (∑ i ∈ Finset.range k, (D + 1) * a i * Q i) =
      (D + 1) * (∑ i ∈ Finset.range k, a i * Q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfac] at hsum
  have hD1 : 0 < D + 1 := by linarith
  have hsmall := mul_le_mul_of_nonneg_left hsum (div_nonneg hD hD1.le)
  have hcancel : D / (D + 1) * ((D + 1) *
      (∑ i ∈ Finset.range k, a i * Q i)) =
      D * (∑ i ∈ Finset.range k, a i * Q i) := by field_simp
  rw [hcancel] at hsmall
  have htotal := hsmall.trans hfirst
  have heq : D * (∑ i ∈ Finset.range k, (a i / m) * (Q i / Qm)) =
      (D * (∑ i ∈ Finset.range k, a i * Q i)) / (m * Qm) := by
    have hs : (∑ i ∈ Finset.range k, (a i / m) * (Q i / Qm)) =
        (∑ i ∈ Finset.range k, a i * Q i) / (m * Qm) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [heq]
  exact (div_le_iff₀ (mul_pos hm hQm)).mpr (by simpa only [mul_comm] using htotal)

/-- Substituting lower bounds for Q_i/Q_m requires nonnegative increments. -/
theorem finite_partition_ratio_lower_bound (a Q L : ℕ → ℝ) (k : ℕ)
    {D m Qm U : ℝ} (hD : 0 ≤ D) (hm : 0 < m)
    (ha : ∀ i < k, 0 ≤ a i)
    (hL : ∀ i < k, L i ≤ Q i / Qm)
    (hU : D * (∑ i ∈ Finset.range k, (a i / m) * (Q i / Qm)) ≤ U) :
    D * (∑ i ∈ Finset.range k, (a i / m) * L i) ≤ U := by
  apply le_trans _ hU
  apply mul_le_mul_of_nonneg_left _ hD
  apply Finset.sum_le_sum
  intro i hi
  have hik := Finset.mem_range.mp hi
  exact mul_le_mul_of_nonneg_left (hL i hik) (div_nonneg (ha i hik) hm.le)

/-- A scaled test in degree j yields the manuscript's auxiliary-degree ratio.
The test inequality and the attained degree-m objective are explicit inputs. -/
theorem auxiliary_degree_weight_ratio {Nj Nm Qj Qm fj fm A t s : ℝ}
    (hNj : 0 < Nj) (hNm : 0 < Nm) (hQm : 0 < Qm)
    (htest : fj ≤ Real.exp (s * A / t) / Nj * Qj)
    (hfm : fm = Real.exp (A / t) / Nm * Qm) :
    (Nj / Nm) * (fj / fm) * Real.exp ((1 - s) * A / t) ≤ Qj / Qm := by
  have he : Real.exp ((1 - s) * A / t) =
      Real.exp (A / t) / Real.exp (s * A / t) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hE : 0 < Real.exp (s * A / t) := Real.exp_pos _
  have hM : Real.exp (A / t) ≠ 0 := (Real.exp_pos _).ne'
  have hmul : Nj * fj ≤ Real.exp (s * A / t) * Qj := by
    have h := mul_le_mul_of_nonneg_left htest hNj.le
    have heq : Nj * (Real.exp (s * A / t) / Nj * Qj) =
        Real.exp (s * A / t) * Qj := by field_simp
    rwa [heq] at h
  calc
    _ = (Nj * fj) / (Real.exp (s * A / t) * Qm) := by
      rw [he, hfm]
      field_simp
    _ ≤ Qj / Qm := by
      apply (div_le_div_iff₀ (mul_pos hE hQm) hQm).mpr
      nlinarith [mul_le_mul_of_nonneg_right hmul hQm.le]

/-- Polynomial replacement of the exponential factor; valid for every real c. -/
theorem auxiliary_ratio_linear_lower_bound {s c R F Q : ℝ}
    (hR : 0 ≤ R) (hF : 0 ≤ F)
    (hQ : R * F * Real.exp ((1 - s) * c) ≤ Q) :
    R * F * (1 + (1 - s) * c) ≤ Q := by
  apply le_trans _ hQ
  exact mul_le_mul_of_nonneg_left
    (by simpa only [add_comm] using Real.add_one_le_exp ((1 - s) * c))
    (mul_nonneg hR hF)

theorem weightedSliceMoment_nonneg {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ)
    (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p) :
    0 ≤ weightedSliceMoment Γ j w := by
  unfold weightedSliceMoment
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hw p) (pow_nonneg (sliceRadius_nonneg _) _)

noncomputable def weightedTangentialSum {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ)
    (w : (Fin r → ℤ) → ℝ) : ℝ := ∑ a ∈ Γ j, w a.1 * (∑ i, (a.2 i : ℝ))

/-- Relate the simplex cost to the same Q and tangential sum used by the
normalized objective, rather than treating them as unrelated numerical inputs. -/
theorem weighted_slice_cost_eq_tangential_sum {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ)
    (w : (Fin r → ℤ) → ℝ) :
    (∑ p ∈ exponentSupport Γ j, w p *
      (∑ γ ∈ exponentSlice Γ j p, ((∑ i, (γ i : ℝ)) + (d + 1 : ℝ)))) =
      weightedTangentialSum Γ j w + (d + 1 : ℝ) * weightedSliceCount Γ j w := by
  rw [show (∑ p ∈ exponentSupport Γ j, w p *
      (∑ γ ∈ exponentSlice Γ j p, ((∑ i, (γ i : ℝ)) + (d + 1 : ℝ)))) =
      (∑ p ∈ exponentSupport Γ j,
        ∑ γ ∈ exponentSlice Γ j p, w p * ((∑ i, (γ i : ℝ)) + (d + 1 : ℝ))) by
    simp only [Finset.mul_sum]]
  rw [sum_exponentSlices, weightedSliceCount_eq_sum]
  unfold weightedTangentialSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The paper's finite inequality for the actual exponent family at arbitrary
partition degrees. The geometric uniform slice inputs remain explicit. -/
theorem slice_partition_moment_bound {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice Γ q 0))
    (j : ℕ → ℕ) (k m : ℕ) (hm : 0 < m) (hj : Monotone j) (hjm : j k = m)
    (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hstep : ∀ i < k, H + h₀ ≤ j (i + 1) - j i)
    (hr : ∀ i < k, 0 ≤ lam * (j (i + 1) - j i : ℕ) - (C + lam * h₀))
    (hQm : 0 < weightedSliceCount Γ m w)
    (hnonneg : ∀ p ∈ exponentSupport Γ m, ∀ γ ∈ exponentSlice Γ m p, ∀ i, 0 ≤ γ i) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range k,
      ((lam * (j (i + 1) - j i : ℕ) - (C + lam * h₀)) / m) *
        (weightedSliceCount Γ (j i) w / weightedSliceCount Γ m w)) ≤
      weightedTangentialSum Γ m w / ((m : ℝ) * weightedSliceCount Γ m w) +
        (d + 1 : ℝ) / m := by
  apply finite_partition_moment_bound
    (fun i => weightedSliceMoment Γ (j i) w)
    (fun i => weightedSliceCount Γ (j i) w)
    (fun i => lam * (j (i + 1) - j i : ℕ) - (C + lam * h₀)) k
    (by positivity) (by exact_mod_cast hm) hQm (weightedSliceMoment_nonneg Γ (j 0) w hw)
  · intro i hi
    have h := weightedSliceMoment_growth Γ hΓ H h₀ hcube hlam hH hlower (j i)
      (j (i + 1) - j i) w (hstep i hi) (hr i hi) hw
    rw [Nat.add_sub_of_le (hj (Nat.le_succ i))] at h
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  · rw [hjm]
    have h := weighted_exponentSlice_firstMoment_bound Γ m w hw hnonneg
    rw [weighted_slice_cost_eq_tangential_sum] at h
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have heq : (m : ℝ) * weightedSliceCount Γ m w *
        (weightedTangentialSum Γ m w / ((m : ℝ) * weightedSliceCount Γ m w) +
          (d + 1 : ℝ) / m) =
        weightedTangentialSum Γ m w + (d + 1 : ℝ) * weightedSliceCount Γ m w := by
      field_simp
    rw [heq]
    simpa only [add_assoc, one_add_one_eq_two] using h

end MixedFujita
