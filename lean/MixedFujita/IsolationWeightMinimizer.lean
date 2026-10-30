/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IsolationDivisorStructure
public import MixedFujita.FirstVariation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
The minimizer of the exponential objective on the weights of a simple normal crossing family, and
its first-order conditions (step 11, sections 3.2 and 6.1 of the manuscript for a fixed basis).

Fix sections s_1, …, s_N with zero divisors D_i on a simple normal crossing model, with
e_ik the coefficient of D_i at the member ξ_k and a_k the log discrepancy of ξ_k. A monomial
valuation with weights w_k ≥ 0 on the members through one point has log discrepancy
A(w) = Σ_k w_k a_k and values v_i(w) = Σ_k w_k e_ik on the sections, and the objective of
section 3 is

  F(w) = Σ_i exp(A(w)/t − v_i(w)/j).

* If one section does not vanish over Φ (e_{i₀ k} = 0 for the members meeting Φ), then F is
  coercive on the weights supported on the members through a point of Φ, and a minimizer exists;
  it is nonzero as soon as F takes a value smaller than N = F(0) (the interior condition (7)).
* At a nonzero minimizer w put q_i = v_i(w)/A(w) and
  c_i = (t/j) exp(−v_i(w)/j) / Σ_h exp(−v_h(w)/j). Then c_i > 0, j Σ c_i = t, c · q = 1
  (stationarity in the scale), q lies in the polytope of a point of Φ, and c · z_k ≤ 1 for every
  member through a point of Φ whose polytope contains q (the inequality (24): the minimizer can be
  moved to that point without changing A and the v_i, and the weight of the member increased).

These are the data of the minimizer used in section 6, except for the point-centre property.

* Retraction (11) in the form of the objective: for a prime divisor of any smooth birational model
  whose centre meets Φ, with any nonnegative scale, there is a weight over Φ on the family whose
  objective is at most that of the scaled prime divisor. So the minimum over the weights is a
  lower bound for the objective on all divisorial valuations with centre meeting Φ. The same holds
  for a prime divisor of a smooth birational test model of the base Y of a proper simple normal
  crossing model π : X → Y (proper or not) whose centre contains the point x, with Φ = π⁻¹(x).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Analysis

variable {N r : ℕ}

/-- The exponential objective on weights: Σ_i exp(A(w)/t − v_i(w)/j) with A(w) = Σ_k w_k a_k and
v_i(w) = Σ_k w_k e_ik. -/
noncomputable def weightExponentialObjective (a : Fin r → ℝ) (e : Fin N → Fin r → ℝ) (t j : ℝ)
    (w : Fin r → ℝ) : ℝ :=
  ∑ i, Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i k) / j)

/-- The coefficients c_i = (t/j) exp(−v_i(w)/j) / Σ_h exp(−v_h(w)/j) of a weight. -/
noncomputable def weightExponentialCoefficient (e : Fin N → Fin r → ℝ) (t j : ℝ)
    (w : Fin r → ℝ) (i : Fin N) : ℝ :=
  t / j * (Real.exp (-(∑ k, w k * e i k) / j) / ∑ h, Real.exp (-(∑ k, w k * e h k) / j))

/-- A right minimum of a sum of exponentials along a line has nonnegative derivative. -/
theorem exponentialSum_directional_nonneg (t j A α : ℝ) (v β : Fin N → ℝ)
    (hmin : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∑ i, Real.exp (A / t - v i / j) ≤
      ∑ i, Real.exp ((A + ε * α) / t - (v i + ε * β i) / j)) :
    0 ≤ ∑ i, Real.exp (A / t - v i / j) * (α / t - β i / j) := by
  have hF : HasDerivWithinAt
      (fun ε : ℝ => ∑ i, Real.exp ((A + ε * α) / t - (v i + ε * β i) / j))
      (∑ i, Real.exp ((A + 0 * α) / t - (v i + 0 * β i) / j) * (α / t - β i / j))
      (Set.Ioi 0) 0 := by
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have hA : HasDerivAt (fun ε : ℝ => A + ε * α) α 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const α).const_add A
    have hv : HasDerivAt (fun ε : ℝ => v i + ε * β i) (β i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (β i)).const_add (v i)
    exact ((hA.div_const t).sub (hv.div_const j)).exp.hasDerivWithinAt
  have h0 := right_derivative_nonneg_of_minimum hF (by
    filter_upwards [hmin] with ε hε
    simpa only [zero_mul, add_zero] using hε)
  simpa only [zero_mul, add_zero] using h0

/-- The first-order inequality in the form of the coefficients c_i: Σ_i c_i β_i ≤ α. -/
theorem exponentialSum_coefficient_le (hN : 0 < N) {t j : ℝ} (ht : 0 < t) (hj : 0 < j)
    (A α : ℝ) (v β : Fin N → ℝ)
    (h : 0 ≤ ∑ i, Real.exp (A / t - v i / j) * (α / t - β i / j)) :
    ∑ i, t / j * (Real.exp (-v i / j) / ∑ h, Real.exp (-v h / j)) * β i ≤ α := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hS : 0 < ∑ h, Real.exp (-v h / j) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hfac : ∑ i, Real.exp (A / t - v i / j) * (α / t - β i / j) =
      Real.exp (A / t) * (α / t * (∑ h, Real.exp (-v h / j)) -
        (∑ i, β i * Real.exp (-v i / j)) / j) := by
    rw [mul_sub, Finset.mul_sum, Finset.sum_div, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_eq_add_neg (A / t), Real.exp_add, ← neg_div]
    ring
  rw [hfac] at h
  have h1 : 0 ≤ α / t * (∑ h, Real.exp (-v h / j)) - (∑ i, β i * Real.exp (-v i / j)) / j :=
    nonneg_of_mul_nonneg_right h (Real.exp_pos _)
  have h2 : (∑ i, β i * Real.exp (-v i / j)) / j ≤ α / t * ∑ h, Real.exp (-v h / j) :=
    sub_nonneg.mp h1
  have hsum : ∑ i, t / j * (Real.exp (-v i / j) / ∑ h, Real.exp (-v h / j)) * β i =
      t / (∑ h, Real.exp (-v h / j)) * ((∑ i, β i * Real.exp (-v i / j)) / j) := by
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hsum]
  calc t / (∑ h, Real.exp (-v h / j)) * ((∑ i, β i * Real.exp (-v i / j)) / j)
      ≤ t / (∑ h, Real.exp (-v h / j)) * (α / t * ∑ h, Real.exp (-v h / j)) :=
        mul_le_mul_of_nonneg_left h2 (div_pos ht hS).le
    _ = α := by
        field_simp

/-- The coefficients of a weight are positive and j Σ c_i = t. -/
theorem weightExponentialCoefficient_pos (hN : 0 < N) (e : Fin N → Fin r → ℝ) {t j : ℝ}
    (ht : 0 < t) (hj : 0 < j) (w : Fin r → ℝ) (i : Fin N) :
    0 < weightExponentialCoefficient e t j w i := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact mul_pos (div_pos ht hj) (div_pos (Real.exp_pos _)
    (Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty))

theorem weightExponentialCoefficient_sum (hN : 0 < N) (e : Fin N → Fin r → ℝ) {t j : ℝ}
    (hj : 0 < j) (w : Fin r → ℝ) :
    j * ∑ i, weightExponentialCoefficient e t j w i = t := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hS : 0 < ∑ h, Real.exp (-(∑ k, w k * e h k) / j) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  unfold weightExponentialCoefficient
  rw [← Finset.mul_sum, ← Finset.sum_div, div_self hS.ne', mul_one]
  field_simp

/-- Stationarity in the scale: if F(λ w) ≥ F(w) for all λ > 0 then Σ_i c_i v_i(w) = A(w). -/
theorem weightExponentialCoefficient_scale (hN : 0 < N) (a : Fin r → ℝ)
    (e : Fin N → Fin r → ℝ) {t j : ℝ} (ht : 0 < t) (hj : 0 < j) (w : Fin r → ℝ)
    (hscale : ∀ lam : ℝ, 0 < lam →
      weightExponentialObjective a e t j w ≤ weightExponentialObjective a e t j (lam • w)) :
    ∑ i, weightExponentialCoefficient e t j w i * (∑ k, w k * e i k) = ∑ k, w k * a k := by
  have hobj : ∀ lam : ℝ, weightExponentialObjective a e t j (lam • w) =
      ∑ i, Real.exp ((lam * ∑ k, w k * a k) / t - (lam * ∑ k, w k * e i k) / j) := by
    intro lam
    unfold weightExponentialObjective
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have hobj1 : weightExponentialObjective a e t j w =
      ∑ i, Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i k) / j) := rfl
  -- increasing the scale
  have hup := exponentialSum_directional_nonneg t j (∑ k, w k * a k) (∑ k, w k * a k)
    (fun i => ∑ k, w k * e i k) (fun i => ∑ k, w k * e i k) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h := hscale (1 + ε) (by linarith [Set.mem_Ioi.mp hε])
      rw [hobj, hobj1] at h
      refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      ring_nf)
  -- decreasing the scale
  have hdown := exponentialSum_directional_nonneg t j (∑ k, w k * a k) (-(∑ k, w k * a k))
    (fun i => ∑ k, w k * e i k) (fun i => -(∑ k, w k * e i k)) (by
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
      have h := hscale (1 - ε) (by linarith [hε.2])
      rw [hobj, hobj1] at h
      refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
      ring_nf)
  have h1 := exponentialSum_coefficient_le hN ht hj _ _ _ _ hup
  have h2 := exponentialSum_coefficient_le hN ht hj _ _ _ _ hdown
  have h2' : -(∑ i, t / j * (Real.exp (-(∑ k, w k * e i k) / j) /
      ∑ h, Real.exp (-(∑ k, w k * e h k) / j)) * (∑ k, w k * e i k)) ≤ -(∑ k, w k * a k) := by
    rw [← Finset.sum_neg_distrib]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) h2
    ring
  exact le_antisymm h1 (neg_le_neg_iff.mp h2')

/-- The inequality (24) in the direction of one coordinate: if w' has the same A and the same v_i
as w and F(w' + ε e_k) ≥ F(w) for all ε > 0, then Σ_i c_i e_ik ≤ a_k. -/
theorem weightExponentialCoefficient_direction (hN : 0 < N) (a : Fin r → ℝ)
    (e : Fin N → Fin r → ℝ) {t j : ℝ} (ht : 0 < t) (hj : 0 < j) (w w' : Fin r → ℝ)
    (hA : ∑ k, w' k * a k = ∑ k, w k * a k)
    (hv : ∀ i, ∑ k, w' k * e i k = ∑ k, w k * e i k) (k₀ : Fin r)
    (hdir : ∀ ε : ℝ, 0 < ε → weightExponentialObjective a e t j w ≤
      weightExponentialObjective a e t j (fun k => w' k + if k = k₀ then ε else 0)) :
    ∑ i, weightExponentialCoefficient e t j w i * e i k₀ ≤ a k₀ := by
  have hsum : ∀ (ε : ℝ) (b : Fin r → ℝ),
      ∑ k, (w' k + if k = k₀ then ε else 0) * b k = ∑ k, w' k * b k + ε * b k₀ := by
    intro ε b
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have h := exponentialSum_directional_nonneg t j (∑ k, w k * a k) (a k₀)
    (fun i => ∑ k, w k * e i k) (fun i => e i k₀) (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h := hdir ε (Set.mem_Ioi.mp hε)
      refine h.trans (le_of_eq ?_)
      unfold weightExponentialObjective
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsum ε a, hsum ε (e i), hA, hv i])
  exact exponentialSum_coefficient_le hN ht hj _ _ _ _ h

/-- Existence of a minimizer on a closed set of nonnegative weights on which one of the v_i
vanishes: the objective is at least exp(A(w)/t) there, so its sublevel sets are bounded. -/
theorem exists_weightExponentialObjective_minimizer (a : Fin r → ℝ) (ha : ∀ k, 0 < a k)
    (e : Fin N → Fin r → ℝ) {t j : ℝ} (ht : 0 < t) (Adm : Set (Fin r → ℝ))
    (hclosed : IsClosed Adm) (hnn : ∀ w ∈ Adm, ∀ k, 0 ≤ w k) (i₀ : Fin N)
    (hi₀ : ∀ w ∈ Adm, ∑ k, w k * e i₀ k = 0) (w₁ : Fin r → ℝ) (hw₁ : w₁ ∈ Adm) :
    ∃ w ∈ Adm, ∀ w' ∈ Adm,
      weightExponentialObjective a e t j w ≤ weightExponentialObjective a e t j w' := by
  have hlow : ∀ w ∈ Adm, Real.exp ((∑ k, w k * a k) / t) ≤ weightExponentialObjective a e t j w := by
    intro w hw
    have hterm : Real.exp ((∑ k, w k * a k) / t) =
        Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i₀ k) / j) := by
      rw [hi₀ w hw, zero_div, sub_zero]
    rw [hterm]
    exact Finset.single_le_sum (f := fun i =>
      Real.exp ((∑ k, w k * a k) / t - (∑ k, w k * e i k) / j))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ i₀)
  have hpos₁ : 0 < weightExponentialObjective a e t j w₁ :=
    lt_of_lt_of_le (Real.exp_pos _) (hlow w₁ hw₁)
  -- the bound on the log discrepancy of the points of the sublevel set
  have hbound : ∀ w ∈ Adm, weightExponentialObjective a e t j w ≤
      weightExponentialObjective a e t j w₁ →
      ∑ k, w k * a k ≤ t * Real.log (weightExponentialObjective a e t j w₁) := by
    intro w hw hle
    have h1 := (hlow w hw).trans hle
    have h2 := (Real.le_log_iff_exp_le hpos₁).mpr h1
    rw [div_le_iff₀ ht] at h2
    linarith
  have hcoord : ∀ w ∈ Adm, ∀ k, w k * a k ≤ ∑ k, w k * a k := fun w hw k =>
    Finset.single_le_sum (f := fun k => w k * a k)
      (fun k _ => mul_nonneg (hnn w hw k) (ha k).le) (Finset.mem_univ k)
  let L : ℝ := t * Real.log (weightExponentialObjective a e t j w₁)
  let Kset : Set (Fin r → ℝ) := Adm ∩ {w | ∀ k, w k * a k ≤ L}
  have hKclosed : IsClosed Kset := by
    refine hclosed.inter ?_
    have : {w : Fin r → ℝ | ∀ k, w k * a k ≤ L} = ⋂ k, {w | w k * a k ≤ L} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun k =>
      isClosed_le ((continuous_apply k).mul continuous_const) continuous_const
  have hKsub : Kset ⊆ Set.pi Set.univ fun k => Set.Icc 0 (L / a k) := by
    intro w hw k _
    exact ⟨hnn w hw.1 k, (le_div_iff₀ (ha k)).mpr (hw.2 k)⟩
  have hKcompact : IsCompact Kset :=
    (isCompact_univ_pi fun k => isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hw₁K : w₁ ∈ Kset :=
    ⟨hw₁, fun k => (hcoord w₁ hw₁ k).trans (hbound w₁ hw₁ le_rfl)⟩
  have hcont : Continuous (weightExponentialObjective a e t j) := by
    unfold weightExponentialObjective
    fun_prop
  obtain ⟨w, hwK, hwmin⟩ := hKcompact.exists_isMinOn ⟨w₁, hw₁K⟩ hcont.continuousOn
  refine ⟨w, hwK.1, fun w' hw' => ?_⟩
  by_cases hK' : w' ∈ Kset
  · exact hwmin hK'
  · have hnot : ¬ weightExponentialObjective a e t j w' ≤
        weightExponentialObjective a e t j w₁ := fun hle =>
      hK' ⟨hw', fun k => (hcoord w' hw' k).trans (hbound w' hw' hle)⟩
    exact (hwmin hw₁K).trans (not_le.mp hnot).le

end Analysis

section Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- The weights supported on the members through one point of Φ form a closed set. -/
theorem isClosed_sncWeights {r : ℕ} (ξ : Fin r → X) (Φ : Set X) :
    IsClosed {w : Fin r → ℝ | (∀ k, 0 ≤ w k) ∧
      ∃ p ∈ Φ, ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} := by
  classical
  have hset : {w : Fin r → ℝ | (∀ k, 0 ≤ w k) ∧
      ∃ p ∈ Φ, ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)} =
      ⋃ J : Finset (Fin r), {w : Fin r → ℝ | (∃ p ∈ Φ, ∀ k ∈ J, p ∈ closure ({ξ k} : Set X)) ∧
        (∀ k, 0 ≤ w k) ∧ ∀ k, k ∉ J → w k = 0} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, p, hp, hsupp⟩
      refine ⟨Finset.univ.filter fun k => w k ≠ 0, ⟨p, hp, fun k hk => ?_⟩, h0, fun k hk => ?_⟩
      · exact hsupp k (Finset.mem_filter.mp hk).2
      · by_contra hne
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hne⟩)
    · rintro ⟨J, ⟨p, hp, hJ⟩, h0, hzero⟩
      refine ⟨h0, p, hp, fun k hk => hJ k ?_⟩
      by_contra hkJ
      exact hk (hzero k hkJ)
  rw [hset]
  refine isClosed_iUnion_of_finite fun J => ?_
  by_cases hJ : ∃ p ∈ Φ, ∀ k ∈ J, p ∈ closure ({ξ k} : Set X)
  · have : {w : Fin r → ℝ | (∃ p ∈ Φ, ∀ k ∈ J, p ∈ closure ({ξ k} : Set X)) ∧
        (∀ k, 0 ≤ w k) ∧ ∀ k, k ∉ J → w k = 0} =
        (⋂ k, {w : Fin r → ℝ | 0 ≤ w k}) ∩ ⋂ k, {w : Fin r → ℝ | k ∉ J → w k = 0} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hJ, h.1, h.2⟩⟩
    rw [this]
    refine (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_iInter fun k => ?_)
    by_cases hk : k ∈ J
    · simp only [hk, not_true_eq_false, false_imp_iff, Set.ofPred_true]
      exact isClosed_univ
    · simp only [hk, not_false_eq_true, true_imp_iff]
      exact isClosed_eq (continuous_apply k) continuous_const
  · have : {w : Fin r → ℝ | (∃ p ∈ Φ, ∀ k ∈ J, p ∈ closure ({ξ k} : Set X)) ∧
        (∀ k, 0 ≤ w k) ∧ ∀ k, k ∉ J → w k = 0} = ∅ := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => absurd h hJ
    rw [this]
    exact isClosed_empty

/-- Existence of a nonzero minimizer of the exponential objective on the weights of the simple
normal crossing family over Φ: if some section does not vanish over Φ and the objective takes a
value smaller than N on the weights over Φ (the interior condition). -/
theorem exists_sncWeight_minimizer {N r : ℕ} (ξ : Fin r → X) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X) (hb : ∀ k, cartierCoefficient B (ξ k) < (d : ℤ))
    (Dv : Fin N → CartierDivisor X) (Φ : Set X) {t : ℝ} (ht : 0 < t) (j : ℝ)
    (i₀ : Fin N)
    (hi₀ : ∀ k, (closure ({ξ k} : Set X) ∩ Φ).Nonempty → cartierCoefficient (Dv i₀) (ξ k) = 0)
    (w₁ : Fin r → ℝ) (hw₁0 : ∀ k, 0 ≤ w₁ k)
    (hw₁Φ : ∃ p ∈ Φ, ∀ k, w₁ k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    (hint : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w₁ < N) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ Φ, ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧ (∃ k, w k ≠ 0) ∧
      ∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
        (∃ p ∈ Φ, ∀ k, w' k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w ≤
        weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w' := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set a : Fin r → ℝ := fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d with ha_def
  set e : Fin N → Fin r → ℝ := fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ) with he_def
  have ha : ∀ k, 0 < a k := fun k => by
    have h : (cartierCoefficient B (ξ k) : ℝ) < (d : ℝ) := by exact_mod_cast hb k
    exact div_pos (by linarith) hdpos
  let Adm : Set (Fin r → ℝ) := {w | (∀ k, 0 ≤ w k) ∧
    ∃ p ∈ Φ, ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)}
  have hAdm_i₀ : ∀ w ∈ Adm, ∑ k, w k * e i₀ k = 0 := by
    rintro w ⟨-, p, hp, hsupp⟩
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : w k = 0
    · rw [hk, zero_mul]
    · have h0 := hi₀ k ⟨p, hsupp k hk, hp⟩
      change w k * ((cartierCoefficient (Dv i₀) (ξ k) : ℤ) : ℝ) = 0
      rw [h0, Int.cast_zero, mul_zero]
  obtain ⟨w, hwAdm, hwmin⟩ := exists_weightExponentialObjective_minimizer a ha e (j := j) ht
    Adm (isClosed_sncWeights ξ Φ) (fun w hw => hw.1) i₀ hAdm_i₀ w₁ ⟨hw₁0, hw₁Φ⟩
  refine ⟨w, hwAdm.1, hwAdm.2, ?_, fun w' hw'0 hw'Φ => hwmin w' ⟨hw'0, hw'Φ⟩⟩
  by_contra hall
  have hzero : w = 0 := funext fun k => by
    by_contra hk
    exact hall ⟨k, hk⟩
  have hF0 : weightExponentialObjective a e t j w = N := by
    rw [hzero]
    simp [weightExponentialObjective]
  have h := hwmin w₁ ⟨hw₁0, hw₁Φ⟩
  rw [hF0] at h
  exact absurd hint (not_lt.mpr h)

/-- The data of the minimizer from a nonzero minimizer w of the exponential objective on the
weights of the simple normal crossing family over Φ (sections 3.2 and 6.1 for a fixed family of
sections): with c_i = (t/j) exp(−v_i(w)/j) / Σ_h exp(−v_h(w)/j) and q_i = v_i(w)/A(w), the vector
c is positive with j Σ c_i = t, c · q = 1, q lies in the polytope of every point of Φ through
whose members w is supported, and c · z_k ≤ 1 for every member through a point of Φ whose polytope
contains q. -/
theorem isolation_data_of_sncWeight_minimizer {N r : ℕ} (hN : 0 < N) (ξ : Fin r → X) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X) (hb : ∀ k, cartierCoefficient B (ξ k) < (d : ℤ))
    (Dv : Fin N → CartierDivisor X) (Φ : Set X) {t : ℝ} (ht : 0 < t) (j : ℕ) (hj : 1 ≤ j)
    (w : Fin r → ℝ) (hw0 : ∀ k, 0 ≤ w k) (y : X) (hy : y ∈ Φ)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) (hwne : ∃ k, w k ≠ 0)
    (hwmin : ∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
      (∃ p ∈ Φ, ∀ k, w' k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
      weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w ≤
      weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w') :
    (∀ i, 0 < weightExponentialCoefficient
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w i) ∧
    ∑ i, weightExponentialCoefficient (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w i *
      ((∑ k, w k * (cartierCoefficient (Dv i) (ξ k) : ℝ)) /
        ∑ k, w k * (((d : ℝ) - cartierCoefficient B (ξ k)) / d)) = 1 ∧
    InSNCProfilePolytope ξ d B Dv (fun i => (∑ k, w k * (cartierCoefficient (Dv i) (ξ k) : ℝ)) /
      ∑ k, w k * (((d : ℝ) - cartierCoefficient B (ξ k)) / d)) y ∧
    (∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv
        (fun i => (∑ k, w k * (cartierCoefficient (Dv i) (ξ k) : ℝ)) /
          ∑ k, w k * (((d : ℝ) - cartierCoefficient B (ξ k)) / d)) p →
      ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, weightExponentialCoefficient
            (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w i *
            (cartierCoefficient (Dv i) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ k)) / d) ∧
    (j : ℝ) * ∑ i, weightExponentialCoefficient
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w i = t := by
  classical
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  set a : Fin r → ℝ := fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d with ha_def
  set e : Fin N → Fin r → ℝ := fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ) with he_def
  have ha : ∀ k, 0 < a k := fun k => by
    have h : (cartierCoefficient B (ξ k) : ℝ) < (d : ℝ) := by exact_mod_cast hb k
    exact div_pos (by linarith) hdpos
  have hApos : 0 < ∑ k, w k * a k := by
    obtain ⟨k₁, hk₁⟩ := hwne
    exact lt_of_lt_of_le (mul_pos (lt_of_le_of_ne (hw0 k₁) (Ne.symm hk₁)) (ha k₁))
      (Finset.single_le_sum (f := fun k => w k * a k)
        (fun k _ => mul_nonneg (hw0 k) (ha k).le) (Finset.mem_univ k₁))
  -- stationarity in the scale
  have hscale := weightExponentialCoefficient_scale hN a e ht hjpos w (fun lam hlam =>
    hwmin (lam • w) (fun k => mul_nonneg hlam.le (hw0 k)) ⟨y, hy, fun k hk => hwy k (by
      intro h0
      exact hk (by simp [h0]))⟩)
  refine ⟨fun i => weightExponentialCoefficient_pos hN e ht hjpos w i, ?_, ?_, ?_,
    weightExponentialCoefficient_sum hN e hjpos w⟩
  · -- c · q = 1
    have : ∑ i, weightExponentialCoefficient e t j w i * ((∑ k, w k * e i k) / ∑ k, w k * a k) =
        (∑ i, weightExponentialCoefficient e t j w i * (∑ k, w k * e i k)) / ∑ k, w k * a k := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hscale, div_self hApos.ne']
  · -- q lies in the polytope of y
    refine ⟨fun k => w k * a k / ∑ k, w k * a k,
      fun k => div_nonneg (mul_nonneg (hw0 k) (ha k).le) hApos.le, ?_, fun k hk => hwy k ?_,
      fun i => ?_⟩
    · rw [← Finset.sum_div, div_self hApos.ne']
    · intro h0
      exact hk (by simp [h0])
    · change (∑ k, w k * e i k) / ∑ k, w k * a k =
        ∑ k, w k * a k / (∑ k, w k * a k) * (e i k / a k)
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hak := (ha k).ne'
      field_simp
  · -- the inequality (24)
    intro p hp hq k₀ hk₀
    obtain ⟨μ, hμ0, hμ1, hμsupp, hμq⟩ := hq
    let w' : Fin r → ℝ := fun k => (∑ k, w k * a k) * μ k / a k
    have hA' : ∑ k, w' k * a k = ∑ k, w k * a k := by
      have h1 : ∀ k, w' k * a k = (∑ k, w k * a k) * μ k := fun k => by
        change (∑ k, w k * a k) * μ k / a k * a k = _
        rw [div_mul_cancel₀ _ (ha k).ne']
      rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, hμ1, mul_one]
    have hv' : ∀ i, ∑ k, w' k * e i k = ∑ k, w k * e i k := by
      intro i
      have h1 : ∀ k, w' k * e i k = (∑ k, w k * a k) * (μ k * (e i k / a k)) := fun k => by
        change (∑ k, w k * a k) * μ k / a k * e i k = _
        ring
      have h2 := hμq i
      change (∑ k, w k * e i k) / ∑ k, w k * a k = ∑ k, μ k * (e i k / a k) at h2
      rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.mul_sum, ← h2,
        mul_div_cancel₀ _ hApos.ne']
    refine weightExponentialCoefficient_direction hN a e ht hjpos w w' hA' hv' k₀ fun ε hε => ?_
    refine hwmin _ (fun k => add_nonneg
      (div_nonneg (mul_nonneg hApos.le (hμ0 k)) (ha k).le) (by split_ifs <;> linarith)) ⟨p, hp,
      fun k hk => ?_⟩
    by_cases hkk : k = k₀
    · rw [hkk]
      exact hk₀
    · apply hμsupp k
      intro hμk
      apply hk
      change (∑ k, w k * a k) * μ k / a k + (if k = k₀ then ε else 0) = 0
      rw [hμk, mul_zero, zero_div, ite_eq_right hkk, add_zero]


/-- The data of the minimizer for a fixed family of sections: if some section does not vanish over
Φ and the objective takes a value smaller than N on the weights over Φ, there are a point y of Φ,
a positive vector c with j Σ c_i = t and a profile q with c · q = 1 in the polytope of y such that
c · z_k ≤ 1 for every member through a point of Φ whose polytope contains q. -/
theorem exists_isolation_data_of_interior {N r : ℕ} (hN : 0 < N) (ξ : Fin r → X) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X) (hb : ∀ k, cartierCoefficient B (ξ k) < (d : ℤ))
    (Dv : Fin N → CartierDivisor X) (Φ : Set X) {t : ℝ} (ht : 0 < t) (j : ℕ) (hj : 1 ≤ j)
    (i₀ : Fin N)
    (hi₀ : ∀ k, (closure ({ξ k} : Set X) ∩ Φ).Nonempty → cartierCoefficient (Dv i₀) (ξ k) = 0)
    (w₁ : Fin r → ℝ) (hw₁0 : ∀ k, 0 ≤ w₁ k)
    (hw₁Φ : ∃ p ∈ Φ, ∀ k, w₁ k ≠ 0 → p ∈ closure ({ξ k} : Set X))
    (hint : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
      (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) t j w₁ < N) :
    ∃ (y : X) (c q : Fin N → ℝ), y ∈ Φ ∧ (∀ i, 0 < c i) ∧ ∑ i, c i * q i = 1 ∧
      InSNCProfilePolytope ξ d B Dv q y ∧
      (∀ p ∈ Φ, InSNCProfilePolytope ξ d B Dv q p → ∀ k, p ∈ closure ({ξ k} : Set X) →
        ∑ i, c i * (cartierCoefficient (Dv i) (ξ k) : ℝ) ≤
          ((d : ℝ) - cartierCoefficient B (ξ k)) / d) ∧
      (j : ℝ) * ∑ i, c i = t := by
  obtain ⟨w, hw0, ⟨y, hy, hwy⟩, hwne, hwmin⟩ := exists_sncWeight_minimizer ξ d hd B hb Dv Φ ht j i₀
    hi₀ w₁ hw₁0 hw₁Φ hint
  obtain ⟨hc, hcq, hqy, hpoly, hsum⟩ := isolation_data_of_sncWeight_minimizer hN ξ d hd B hb Dv Φ
    ht j hj w hw0 y hy hwy hwne hwmin
  exact ⟨y, _, _, hy, hc, hcq, hqy, hpoly, hsum⟩

end Scheme

section Retraction

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Retraction (11) for the objective: a prime divisor t of a smooth birational model whose centre
meets Φ, scaled by lam ≥ 0, has objective Σ_i exp(lam A_t/τ − lam v_i(t)/j) at least the objective
of the weight lam · (orders of the members along t), which is a weight over Φ on the simple normal
crossing family. -/
theorem exists_sncWeight_objective_le_of_prime {N r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ)
    (hd : 1 ≤ d) (B : CartierDivisor X)
    (hB : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (Dv : Fin N → CartierDivisor X)
    (hD : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (Dv i) (z : X) = 0)
    (Φ : Set X) (cT : EtaleChart K T n) (t : CodimensionOnePoint T)
    (hcentre : (closure ({ρ (t : T)} : Set X) ∩ Φ).Nonempty) {τ : ℝ} (hτ : 0 < τ) (j lam : ℝ)
    (hlam : 0 ≤ lam) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ Φ, ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      weightExponentialObjective (fun k => ((d : ℝ) - cartierCoefficient B (ξ k)) / d)
          (fun i k => (cartierCoefficient (Dv i) (ξ k) : ℝ)) τ j w ≤
        ∑ i, Real.exp (lam * (((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
            (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
            cT etaleCharts_cover) (t : T)) / d) / τ -
          lam * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) / j) := by
  obtain ⟨o, ho, hosupp, hpull, hdisc⟩ := exists_snc_orders_at_prime ρ hρ ξ hinj hξ hsnc t
  obtain ⟨p, hpcl, hpΦ⟩ := hcentre
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine ⟨fun k => lam * (o k : ℝ), fun k => mul_nonneg hlam (by exact_mod_cast ho k),
    ⟨p, hpΦ, fun k hk => ?_⟩, ?_⟩
  · have hok : o k ≠ 0 := fun h => hk (by
      change lam * (o k : ℝ) = 0
      rw [h, Int.cast_zero, mul_zero])
    exact closure_minimal (Set.singleton_subset_iff.mpr (hosupp k hok)) isClosed_closure hpcl
  · unfold weightExponentialObjective
    refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
    have hv : ∑ k, lam * (o k : ℝ) * (cartierCoefficient (Dv i) (ξ k) : ℝ) =
        lam * (cartierCoefficient (cartierPullback ρ (Dv i)) (t : T) : ℝ) := by
      rw [hpull (Dv i) (hD i)]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hR : (d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient B (ξ k) : ℝ) * (o k : ℝ) ≤
        (d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T) := by
      exact_mod_cast hdisc c₀ f₀ d B hB cT
    have hA : ∑ k, lam * (o k : ℝ) * (((d : ℝ) - cartierCoefficient B (ξ k)) / d) =
        lam * (((d : ℝ) * ∑ k, (o k : ℝ) -
          ∑ k, (cartierCoefficient B (ξ k) : ℝ) * (o k : ℝ)) / d) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hv, hA]
    have hle : lam * (((d : ℝ) * ∑ k, (o k : ℝ) -
        ∑ k, (cartierCoefficient B (ξ k) : ℝ) * (o k : ℝ)) / d) / τ ≤
        lam * (((d : ℝ) + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d
          (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B)
          cT etaleCharts_cover) (t : T)) / d) / τ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hR hdpos.le) hlam) hτ.le
    linarith

end Retraction

section TestPrime

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Retraction for the objective from a test model of the base: for a proper simple normal
crossing model π : X → Y of a pair, Cartier divisors G_i of Y whose pullbacks are supported on the
family, and a prime divisor e of a smooth birational test model σ : U → Y whose centre contains x,
scaled by lam ≥ 0, there is a weight over π⁻¹(x) on the family whose objective is at most
Σ_i exp(lam A_e/τ − lam v_i(e)/j), with A_e the log discrepancy of e for the pair and v_i(e) the
coefficient of σ*G_i at e. -/
theorem exists_sncWeight_objective_le_of_test_prime {N r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (z : X) = 0)
    (G : Fin N → CartierDivisor Y)
    (hGsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (G i)) (z : X) = 0)
    {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
    [U.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
    (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (x : Y)
    (hx : x ∈ closure ({σ (e : U)} : Set Y)) {τ : ℝ} (hτ : 0 < τ) (j lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      weightExponentialObjective
          (fun k => ((d : ℝ) - cartierCoefficient
            (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d)
          (fun i k => (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ)) τ j w ≤
        ∑ i, Real.exp (lam * (((d : ℝ) + cartierCoefficient
            (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) / d) / τ -
          lam * (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ) / j) := by
  obtain ⟨o, t₀, ht₀, ho, hosupp, hpull, -, hdisc⟩ := exists_snc_orders_at_test_prime π hπ cY fY d
    D cX ξ hinj hξ hsnc hBsupp (fun _ : PUnit.{1} => (0 : CartierDivisor Y))
    (fun _ => CartierDivisor.isEffective_zero) (cartierPullback π 0)
    (cartierPullback_isEffective π 0 CartierDivisor.isEffective_zero)
    (fun t _ => by rw [cartierPullback_zero, cartierCoefficient_zero])
    (by
      rw [effectiveCartierIdealSheaf_cartierPullback π 0 CartierDivisor.isEffective_zero]
      exact congrArg (fun I : Y.IdealSheafData => I.comap π) (iSup_const (ι := PUnit.{1})).symm)
    σ hσ cU e
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  -- a point of the model over x in the closure of the centre
  have hclosed : IsClosed (π '' closure ({t₀} : Set X)) :=
    (Scheme.Hom.isClosedMap π) _ isClosed_closure
  have hxim : x ∈ π '' closure ({t₀} : Set X) := by
    refine closure_minimal (Set.singleton_subset_iff.mpr ?_) hclosed hx
    exact ⟨t₀, subset_closure rfl, ht₀⟩
  obtain ⟨p, hpcl, hpx⟩ := hxim
  refine ⟨fun k => lam * (o k : ℝ), fun k => mul_nonneg hlam (by exact_mod_cast ho k),
    ⟨p, hpx, fun k hk => ?_⟩, ?_⟩
  · have hok : o k ≠ 0 := fun h => hk (by
      change lam * (o k : ℝ) = 0
      rw [h, Int.cast_zero, mul_zero])
    exact closure_minimal (Set.singleton_subset_iff.mpr (hosupp k hok)) isClosed_closure hpcl
  · unfold weightExponentialObjective
    refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_
    have hv : ∑ k, lam * (o k : ℝ) * (cartierCoefficient (cartierPullback π (G i)) (ξ k) : ℝ) =
        lam * (cartierCoefficient (cartierPullback σ (G i)) (e : U) : ℝ) := by
      rw [hpull (G i) (hGsupp i)]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hR : (d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k) : ℝ) * (o k : ℝ) ≤
        (d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U) := by
      exact_mod_cast hdisc
    have hA : ∑ k, lam * (o k : ℝ) * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k)) / d) =
        lam * (((d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k) : ℝ) *
            (o k : ℝ)) / d) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hv, hA]
    have hle : lam * (((d : ℝ) * ∑ k, (o k : ℝ) - ∑ k, (cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D cX etaleCharts_cover) (ξ k) : ℝ) *
          (o k : ℝ)) / d) / τ ≤
        lam * (((d : ℝ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D cU etaleCharts_cover) (e : U)) / d) / τ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hR hdpos.le) hlam) hτ.le
    linarith

end TestPrime

end MixedFujita
