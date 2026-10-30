/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FirstVariation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Algebra.BigOperators.Field

/-!
The arithmetic of the rational isolation in §6. For the minimizing pair at degree m with
discrepancy a and values v_i = v(s_i), put c_i = (t/m) e^(-v_i/m) / Σ_h e^(-v_h/m) and
q_i = v_i/a. The scale derivative vanishes at the minimum, so c · q = 1 and m Σ c_i = t < b.
Moving the profile from q toward z inside a polytope of realizable profiles cannot lower the
functional, so c · z ≤ 1: the inequality (24). For positive c^0 with c^0 · q^0 = 1, a profile
q' with c^0 · q' ≤ 1, μ = min_{q^0_i > 0} q'_i / q^0_i and r ≤ a, the coefficient
(r/a)((1 - η) c^0 · q' + η μ) is at most 1, with equality only if r = a and q' = q^0: the
inequalities (28) and (29). On the components with profile q^0 and r = a the coefficient of Ψ is
exactly a. The ample margin of (27) is positive for small η, and the floor corrections of §6.3
vanish on S and are nonnegative where Γ < 1.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology Finset

variable {ι : Type*} [Fintype ι]

/-- The weights c_i of §6.1. -/
noncomputable def isolationWeights (t m : ℝ) (v : ι → ℝ) (i : ι) : ℝ :=
  t / m * (Real.exp (-v i / m) / ∑ h, Real.exp (-v h / m))

theorem isolationWeight_sum_pos [Nonempty ι] (m : ℝ) (v : ι → ℝ) :
    0 < ∑ h, Real.exp (-v h / m) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem isolationWeights_pos [Nonempty ι] {t m : ℝ} (ht : 0 < t) (hm : 0 < m) (v : ι → ℝ)
    (i : ι) : 0 < isolationWeights t m v i :=
  mul_pos (div_pos ht hm) (div_pos (Real.exp_pos _) (isolationWeight_sum_pos m v))

theorem isolationWeights_sum [Nonempty ι] (t : ℝ) {m : ℝ} (hm : m ≠ 0) (v : ι → ℝ) :
    m * ∑ i, isolationWeights t m v i = t := by
  have hS := (isolationWeight_sum_pos m v).ne'
  have h1 : ∑ i, Real.exp (-v i / m) / ∑ h, Real.exp (-v h / m) = 1 := by
    rw [← Finset.sum_div, div_self hS]
  simp only [isolationWeights, ← Finset.mul_sum, h1]
  field_simp

/-- The derivative of λ ↦ Σ exp(λ x_i). -/
theorem hasDerivAt_scaled_objective (x : ι → ℝ) (μ : ℝ) :
    HasDerivAt (fun ν => ∑ i, Real.exp (ν * x i)) (∑ i, x i * Real.exp (μ * x i)) μ := by
  have h : ∀ i ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun ν => Real.exp (ν * x i)) (x i * Real.exp (μ * x i)) μ := by
    intro i _
    have h1 := ((hasDerivAt_id' μ).mul_const (x i)).exp
    convert h1 using 1
    ring
  simpa only using HasDerivAt.fun_sum h

/-- §6.1: at a minimum of the scaling, c · q = 1. -/
theorem isolation_profile_dot_eq_one [Nonempty ι] {a t m : ℝ} (ha : 0 < a) (ht : 0 < t)
    (hm : 0 < m) (v : ι → ℝ)
    (hmin : IsLocalMin (fun ν => ∑ i, Real.exp (ν * (a / t - v i / m))) 1) :
    ∑ i, isolationWeights t m v i * (v i / a) = 1 := by
  have hd := hmin.hasDerivAt_eq_zero (hasDerivAt_scaled_objective (fun i => a / t - v i / m) 1)
  simp only [one_mul] at hd
  have hsplit : ∀ i, Real.exp (a / t - v i / m) = Real.exp (a / t) * Real.exp (-v i / m) := by
    intro i
    rw [show a / t - v i / m = a / t + -v i / m by ring, Real.exp_add]
  simp only [hsplit] at hd
  have hd' : ∑ i, (a / t - v i / m) * Real.exp (-v i / m) = 0 := by
    have h2 : Real.exp (a / t) * ∑ i, (a / t - v i / m) * Real.exp (-v i / m) = 0 := by
      rw [Finset.mul_sum, ← hd]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    exact (mul_eq_zero.mp h2).resolve_left (Real.exp_pos _).ne'
  have hSpos : 0 < ∑ h, Real.exp (-v h / m) := isolationWeight_sum_pos m v
  have hbal : a / t * ∑ h, Real.exp (-v h / m) = ∑ i, v i / m * Real.exp (-v i / m) := by
    have h3 : ∑ i, (a / t - v i / m) * Real.exp (-v i / m) =
        a / t * ∑ h, Real.exp (-v h / m) - ∑ i, v i / m * Real.exp (-v i / m) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    linarith [hd', h3]
  have h4 : ∑ i, isolationWeights t m v i * (v i / a) =
      t / (a * ∑ h, Real.exp (-v h / m)) * ∑ i, v i / m * Real.exp (-v i / m) := by
    simp only [isolationWeights]
    generalize hS : ∑ h, Real.exp (-v h / m) = S at hSpos ⊢
    have hS0 : S ≠ 0 := hSpos.ne'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [h4, ← hbal]
  field_simp

/-- §6.1 (24): if moving the profile from q toward z cannot lower the functional, then
c · z ≤ c · q. -/
theorem isolation_direction_le [Nonempty ι] {a t m : ℝ} (ha : 0 < a) (ht : 0 < t) (hm : 0 < m)
    (q z : ι → ℝ)
    (hmin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑ i, Real.exp (a / t - a * q i / m) ≤
      ∑ i, Real.exp (a / t - a * (q i + ε * (z i - q i)) / m)) :
    ∑ i, isolationWeights t m (fun i => a * q i) i * z i ≤
      ∑ i, isolationWeights t m (fun i => a * q i) i * q i := by
  set F : ℝ → ℝ := fun ε => ∑ i, Real.exp (a / t - a * (q i + ε * (z i - q i)) / m) with hF
  set D := ∑ i, (-(a * (z i - q i) / m)) * Real.exp (a / t - a * q i / m) with hD
  have hderiv : HasDerivAt F D 0 := by
    have h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt
        (fun ε => Real.exp (a / t - a * (q i + ε * (z i - q i)) / m))
        ((-(a * (z i - q i) / m)) * Real.exp (a / t - a * q i / m)) 0 := by
      intro i _
      have hlin : HasDerivAt (fun ε : ℝ => a / t - a * (q i + ε * (z i - q i)) / m)
          (-(a * (z i - q i) / m)) 0 := by
        have h1 := (((hasDerivAt_id (0 : ℝ)).mul_const (z i - q i)).const_add (q i)).const_mul a
        have h2 := (h1.div_const m).const_sub (a / t)
        simpa only [id, one_mul, mul_one, neg_div] using h2
      have h3 := hlin.exp
      convert h3 using 1
      rw [zero_mul, add_zero, mul_comm]
    simpa only [hF, hD] using HasDerivAt.fun_sum h
  have hmin' : ∀ᶠ ε : ℝ in 𝓝[>] 0, F 0 ≤ F ε := by
    filter_upwards [hmin] with ε hε
    simpa only [hF, zero_mul, add_zero] using hε
  have hD0 := right_derivative_nonneg_of_minimum hderiv.hasDerivWithinAt hmin'
  set S := ∑ h, Real.exp (-(a * q h) / m) with hS
  have hSpos : 0 < S := isolationWeight_sum_pos m (fun i => a * q i)
  have hsplit : ∀ i, Real.exp (a / t - a * q i / m) =
      Real.exp (a / t) * Real.exp (-(a * q i) / m) := by
    intro i
    rw [show a / t - a * q i / m = a / t + -(a * q i) / m by ring, Real.exp_add]
  have hD' : D = -(a / m) * Real.exp (a / t) *
      ∑ i, (z i - q i) * Real.exp (-(a * q i) / m) := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsplit]
    ring
  have hneg : ∑ i, (z i - q i) * Real.exp (-(a * q i) / m) ≤ 0 := by
    rw [hD'] at hD0
    have hpos : 0 < a / m * Real.exp (a / t) := mul_pos (div_pos ha hm) (Real.exp_pos _)
    by_contra h
    push Not at h
    have : -(a / m) * Real.exp (a / t) * ∑ i, (z i - q i) * Real.exp (-(a * q i) / m) < 0 := by
      have h5 := mul_pos hpos h
      linarith
    linarith
  have hfactor : 0 < t / m / S := div_pos (div_pos ht hm) hSpos
  have hdiff : ∑ i, isolationWeights t m (fun i => a * q i) i * z i -
      ∑ i, isolationWeights t m (fun i => a * q i) i * q i =
      t / m / S * ∑ i, (z i - q i) * Real.exp (-(a * q i) / m) := by
    simp only [isolationWeights, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS]
    field_simp
  have : t / m / S * ∑ i, (z i - q i) * Real.exp (-(a * q i) / m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfactor.le hneg
  linarith

/-- The support of the rational profile q^0. -/
noncomputable def profileSupport (q₀ : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => 0 < q₀ i

theorem mem_profileSupport {q₀ : ι → ℝ} {i : ι} : i ∈ profileSupport q₀ ↔ 0 < q₀ i := by
  classical
  simp [profileSupport]

/-- μ ≤ Σ_{q^0_i > 0} c_i q'_i. -/
theorem isolation_min_ratio_le {c q₀ q' : ι → ℝ} (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i)
    (hcq₀ : ∑ i, c i * q₀ i = 1) (hI : (profileSupport q₀).Nonempty) :
    (profileSupport q₀).inf' hI (fun i => q' i / q₀ i) ≤
      ∑ i ∈ profileSupport q₀, c i * q' i := by
  set μ := (profileSupport q₀).inf' hI (fun i => q' i / q₀ i) with hμ
  have hsupp : ∑ i ∈ profileSupport q₀, c i * q₀ i = 1 := by
    rw [← hcq₀]
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_)
    have h0 : q₀ i = 0 := le_antisymm (not_lt.mp (fun h => hi (mem_profileSupport.mpr h))) (hq₀ i)
    rw [h0, mul_zero]
  have hle : ∀ i ∈ profileSupport q₀, c i * (μ * q₀ i) ≤ c i * q' i := by
    intro i hi
    have hpos := mem_profileSupport.mp hi
    have h1 : μ ≤ q' i / q₀ i := Finset.inf'_le _ hi
    have h2 : μ * q₀ i ≤ q' i := by
      have := mul_le_mul_of_nonneg_right h1 hpos.le
      rwa [div_mul_cancel₀ _ hpos.ne'] at this
    exact mul_le_mul_of_nonneg_left h2 (hc i).le
  calc μ = μ * ∑ i ∈ profileSupport q₀, c i * q₀ i := by rw [hsupp, mul_one]
    _ = ∑ i ∈ profileSupport q₀, c i * (μ * q₀ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ∑ i ∈ profileSupport q₀, c i * q' i := Finset.sum_le_sum hle

theorem isolation_partial_le_dot {c q' : ι → ℝ} (hc : ∀ i, 0 < c i) (hq' : ∀ i, 0 ≤ q' i)
    (s : Finset ι) : ∑ i ∈ s, c i * q' i ≤ ∑ i, c i * q' i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => mul_nonneg (hc i).le (hq' i))

theorem isolation_min_ratio_nonneg {q₀ q' : ι → ℝ} (hq' : ∀ i, 0 ≤ q' i)
    (hI : (profileSupport q₀).Nonempty) :
    0 ≤ (profileSupport q₀).inf' hI (fun i => q' i / q₀ i) := by
  apply Finset.le_inf'
  intro i hi
  exact div_nonneg (hq' i) (mem_profileSupport.mp hi).le

/-- §6.2 (28): the coefficient ratio Ψ_F / a_F is at most 1. -/
theorem isolation_coefficient_le {c q₀ q' : ι → ℝ} (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i)
    (hq' : ∀ i, 0 ≤ q' i) (hcq₀ : ∑ i, c i * q₀ i = 1) (hcq' : ∑ i, c i * q' i ≤ 1)
    (hI : (profileSupport q₀).Nonempty) {η r a : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hr : 0 ≤ r)
    (hra : r ≤ a) (ha : 0 < a) :
    r / a * ((1 - η) * ∑ i, c i * q' i +
      η * (profileSupport q₀).inf' hI (fun i => q' i / q₀ i)) ≤ 1 := by
  set μ := (profileSupport q₀).inf' hI (fun i => q' i / q₀ i)
  have hμ : μ ≤ ∑ i, c i * q' i :=
    (isolation_min_ratio_le hc hq₀ hcq₀ hI).trans (isolation_partial_le_dot hc hq' _)
  have hμ0 : 0 ≤ μ := isolation_min_ratio_nonneg hq' hI
  have hX0 : 0 ≤ ∑ i, c i * q' i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hq' i)
  have hB : (1 - η) * ∑ i, c i * q' i + η * μ ≤ 1 := by nlinarith
  have hB0 : 0 ≤ (1 - η) * ∑ i, c i * q' i + η * μ := by nlinarith
  have hra' : r / a ≤ 1 := (div_le_one ha).mpr hra
  have hra0 : 0 ≤ r / a := div_nonneg hr ha.le
  calc r / a * ((1 - η) * ∑ i, c i * q' i + η * μ) ≤ 1 * 1 :=
        mul_le_mul hra' hB hB0 zero_le_one
    _ = 1 := one_mul 1

/-- §6.2 (29): equality in (28) forces r = a and q' = q^0, so a component meeting S with
coefficient a_F is already a component of S. -/
theorem isolation_coefficient_eq {c q₀ q' : ι → ℝ} (hc : ∀ i, 0 < c i) (hq₀ : ∀ i, 0 ≤ q₀ i)
    (hq' : ∀ i, 0 ≤ q' i) (hcq₀ : ∑ i, c i * q₀ i = 1) (hcq' : ∑ i, c i * q' i ≤ 1)
    (hI : (profileSupport q₀).Nonempty) {η r a : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hr : 0 ≤ r)
    (hra : r ≤ a) (ha : 0 < a)
    (heq : r / a * ((1 - η) * ∑ i, c i * q' i +
      η * (profileSupport q₀).inf' hI (fun i => q' i / q₀ i)) = 1) :
    r = a ∧ q' = q₀ := by
  set μ := (profileSupport q₀).inf' hI (fun i => q' i / q₀ i) with hμdef
  set X := ∑ i, c i * q' i with hX
  have hμ : μ ≤ X :=
    (isolation_min_ratio_le hc hq₀ hcq₀ hI).trans (isolation_partial_le_dot hc hq' _)
  have hμ0 : 0 ≤ μ := isolation_min_ratio_nonneg hq' hI
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hq' i)
  have hra' : r / a ≤ 1 := (div_le_one ha).mpr hra
  have hra0 : 0 ≤ r / a := div_nonneg hr ha.le
  have hB : (1 - η) * X + η * μ ≤ 1 := by nlinarith
  have hB0 : 0 ≤ (1 - η) * X + η * μ := by nlinarith
  -- both factors are 1
  have hB1 : (1 - η) * X + η * μ = 1 := by
    by_contra h
    have hlt : (1 - η) * X + η * μ < 1 := lt_of_le_of_ne hB h
    have : r / a * ((1 - η) * X + η * μ) < 1 := by
      calc r / a * ((1 - η) * X + η * μ) ≤ 1 * ((1 - η) * X + η * μ) :=
            mul_le_mul_of_nonneg_right hra' hB0
        _ < 1 := by linarith
    linarith
  have hra1 : r / a = 1 := by
    rw [hB1, mul_one] at heq
    exact heq
  have hr_eq : r = a := by
    field_simp at hra1
    linarith
  have hμ1 : μ = 1 := by nlinarith
  have hX1 : X = 1 := by nlinarith
  refine ⟨hr_eq, ?_⟩
  -- q'_i ≥ q^0_i on the support, and Σ c (q' - q^0) = 0
  have hge : ∀ i, q₀ i ≤ q' i := by
    intro i
    by_cases hi : 0 < q₀ i
    · have h1 : μ ≤ q' i / q₀ i := Finset.inf'_le _ (mem_profileSupport.mpr hi)
      rw [hμ1, le_div_iff₀ hi, one_mul] at h1
      exact h1
    · have h0 : q₀ i = 0 := le_antisymm (not_lt.mp hi) (hq₀ i)
      rw [h0]
      exact hq' i
  have hsum : ∑ i, c i * (q' i - q₀ i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hX, hX1, hcq₀, sub_self]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hc i).le (sub_nonneg.mpr (hge i)))).mp hsum
  funext i
  have h := hterms i (Finset.mem_univ i)
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' (hc i).ne'
  · linarith

/-- §6.2: on a component with profile q^0 and r_F = a_F the coefficient of Ψ is a_F. -/
theorem isolation_coefficient_on_S {c q₀ : ι → ℝ} (hcq₀ : ∑ i, c i * q₀ i = 1)
    (hI : (profileSupport q₀).Nonempty) (η a : ℝ) {M : ℝ} (hM : 0 < M) :
    (1 - η) * ∑ i, c i * (a * q₀ i) +
      η / M * (profileSupport q₀).inf' hI (fun i => M / q₀ i * (a * q₀ i)) = a := by
  have hconst : (profileSupport q₀).inf' hI (fun i => M / q₀ i * (a * q₀ i)) = M * a := by
    have h : ∀ i ∈ profileSupport q₀, M / q₀ i * (a * q₀ i) = M * a := by
      intro i hi
      have hpos := mem_profileSupport.mp hi
      field_simp
    rw [Finset.inf'_congr hI rfl h, Finset.inf'_const]
  have hsum : ∑ i, c i * (a * q₀ i) = a := by
    have h1 : ∑ i, c i * (a * q₀ i) = a * ∑ i, c i * q₀ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, hcq₀, mul_one]
  rw [hconst, hsum]
  field_simp
  ring

/-- (27): the ample margin b - (1 - η) m Σ c^0 - η u / M is positive for small η. -/
theorem isolation_ample_margin {b s u M : ℝ} (hs : s < b) (hM : 0 < M) :
    ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → 0 < b - (1 - η) * s - η * u / M := by
  set K := |s - u / M| + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨(b - s) / K, div_pos (sub_pos.mpr hs) hK0, fun η hη hηlt => ?_⟩
  have h1 : η * K < b - s := by
    rw [lt_div_iff₀ hK0] at hηlt
    linarith
  have h2 : η * (s - u / M) ≥ -(η * |s - u / M|) := by
    have := neg_abs_le (s - u / M)
    nlinarith
  have h3 : b - (1 - η) * s - η * u / M = (b - s) + η * (s - u / M) := by
    field_simp
    ring
  rw [h3]
  have h4 : η * |s - u / M| < b - s := by nlinarith
  linarith

/-- §6.3: on S the boundary coefficient is (1 - a_F) + a_F = 1, so the correction -⌊Γ⌋ + 1
vanishes. -/
theorem isolation_floor_correction_on_S (a : ℝ) : -⌊(1 - a) + a⌋ + 1 = 0 := by
  have : (1 - a) + a = 1 := by ring
  rw [this, Int.floor_one]
  ring

/-- §6.3: where Γ < 1 the correction -⌊Γ⌋ is nonnegative. -/
theorem isolation_floor_correction_nonneg {Γ : ℝ} (h : Γ < 1) : 0 ≤ -⌊Γ⌋ := by
  have : ⌊Γ⌋ ≤ 0 := by
    have h1 : ⌊Γ⌋ < 1 := Int.floor_lt.mpr (by exact_mod_cast h)
    omega
  omega

end MixedFujita
