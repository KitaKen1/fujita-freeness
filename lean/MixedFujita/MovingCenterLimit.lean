/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DegreeLimits
public import MixedFujita.TaylorPartitionBound

/-!
The limits (22) and (23) of §5.3 with moving centers. Along degrees m_k → ∞ with f_{m_k} → c and
liminf f = c > 0, each minimizing pair whose center has dimension D > 0 carries weighted counts Q,
a normalized tangential moment T and a discrepancy A ≥ a satisfying (16) T ≤ D/t, (20) for the
partition j_i = ⌊m i/l⌋ and (21) against the infima f_j. With the Hilbert asymptotics
N_j/j^n → ν > 0, the coefficients of (20) tend to λ/l and the lower bounds of (21) to
(i/l)^n e^((1 - i/l) a/b) for t ≤ b, so one finite partition with
1/t < λ · (grid sum of s^n e^((1-s) a/b)) gives a contradiction. Extracting a subsequence on which
the center dimension is constant, every minimizing pair along the chosen degrees eventually has a
point center. The partition j_i = ⌊M i/l⌋ satisfies the step conditions of the Taylor form of (20)
once M ≥ l (H + h₀ + λ^(d+1)).
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

theorem auxiliaryDegree_le_self (m i l : ℕ) (hi : i ≤ l) :
    auxiliaryDegree m i l ≤ m :=
  Nat.div_le_of_le_mul (by rw [mul_comm l m]; exact Nat.mul_le_mul_left m hi)

theorem auxiliaryDegree_self (m l : ℕ) (hl : 0 < l) : auxiliaryDegree m l l = m :=
  Nat.mul_div_cancel m hl

/-- The steps of the uniform partition are at least B once m ≥ l B. -/
theorem auxiliaryDegree_step_ge (m i l B : ℕ) (hl : 0 < l) (hm : l * B ≤ m) :
    B ≤ auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l := by
  unfold auxiliaryDegree
  have h1 : m * i / l + m / l ≤ (m * i + m) / l := Nat.div_add_div_le_add_div
  have h2 : B ≤ m / l := (Nat.le_div_iff_mul_le hl).mpr (by rw [mul_comm]; exact hm)
  rw [mul_add, mul_one]
  omega

/-- The Hilbert ratio N_{j_i}/N_m tends to (i/l)^n along any degrees tending to infinity. -/
theorem hilbert_auxiliary_ratio_tendsto (n i l : ℕ) (hi : 0 < i) (hl : 0 < l) (N : ℕ → ℕ)
    {ν : ℝ} (hν : 0 < ν) (hN : Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => (N (auxiliaryDegree (m k) i l) : ℝ) / N (m k)) atTop
      (𝓝 (((i : ℝ) / l) ^ n)) := by
  have hj := (auxiliaryDegree_tendsto_atTop i l hi hl).comp hm
  have h := ((hN.comp hj).div (hN.comp hm) hν.ne').mul
    (((auxiliaryDegree_ratio_tendsto i l hl).comp hm).pow n)
  rw [div_self hν.ne', one_mul] at h
  apply h.congr'
  filter_upwards [hj.eventually (eventually_gt_atTop 0), hm.eventually (eventually_gt_atTop 0)]
    with k hjk hmk
  simp only [Pi.div_apply, Function.comp_apply, div_pow]
  have hj0 : ((auxiliaryDegree (m k) i l : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hjk.ne'
  have hm0 : ((m k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmk.ne'
  by_cases hN0 : (N (m k) : ℝ) = 0
  · simp [hN0]
  · field_simp

/-- The inequalities at one degree m for a minimizing pair whose center has dimension D: the
discrepancy bound a ≤ A, positivity of the weighted counts Q, (16) T ≤ D/t, (20) for the
partition j_i = ⌊m i/l⌋, and (21) against the infima f_j. -/
def CenterDegreeInequalities (N : ℕ → ℕ) (f : ℕ → ℝ) (t lam C a : ℝ) (l m D : ℕ)
    (Q : ℕ → ℝ) (T A : ℝ) : Prop :=
  a ≤ A ∧ (∀ j, 0 ≤ Q j) ∧ 0 < Q m ∧ T ≤ D / t ∧
    (D : ℝ) * ∑ i ∈ Finset.range l, ((lam * ((auxiliaryDegree m (i + 1) l -
      auxiliaryDegree m i l : ℕ) : ℝ) - C) / m) * (Q (auxiliaryDegree m i l) / Q m) ≤
        T + D / m ∧
    ∀ i ∈ Finset.Ico 1 l, ((N (auxiliaryDegree m i l) : ℝ) / N m) *
      (f (auxiliaryDegree m i l) / f m) *
        Real.exp ((1 - (auxiliaryDegree m i l : ℝ) / m) * A / t) ≤
      Q (auxiliaryDegree m i l) / Q m

/-- (22) and (23) at one finite partition: the inequalities cannot hold along a degree sequence
for a fixed center dimension D > 0. -/
theorem moving_center_partition_contradiction (n l D : ℕ) (hn : 0 < n) (hl : 2 ≤ l)
    (hD : 0 < D) (N : ℕ → ℕ) {ν : ℝ} (hν : 0 < ν)
    (hN : Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν))
    (f : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hliminf : liminf f atTop = c)
    (hbdd : IsBoundedUnder (· ≥ ·) atTop f)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hfm : Tendsto (fun k => f (m k)) atTop (𝓝 c))
    {lam C t b a : ℝ} (hlam : 0 < lam) (ht : 0 < t) (htb : t ≤ b) (ha : 0 < a)
    (hgap : 1 / t < lam * uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * (a / b))) l)
    (Q : ℕ → ℕ → ℝ) (T A : ℕ → ℝ)
    (hineq : ∀ᶠ k in atTop, CenterDegreeInequalities N f t lam C a l (m k) D (Q k) (T k) (A k)) :
    False := by
  have hl0 : 0 < l := by omega
  set jd : ℕ → ℕ → ℕ := fun i k => auxiliaryDegree (m k) i l with hjd
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hmpos : ∀ᶠ k in atTop, 0 < m k := hm.eventually (eventually_gt_atTop 0)
  -- the coefficients of (20) tend to lam/l and are eventually positive
  have hcoef : ∀ i, Tendsto (fun k => (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k)
      atTop (𝓝 (lam / l)) := fun i => (adjusted_auxiliary_step_tendsto i l hl0 lam C).comp hm
  have hcoefpos : ∀ i, ∀ᶠ k in atTop,
      0 ≤ (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k := fun i =>
    ((hcoef i).eventually (lt_mem_nhds (by positivity))).mono fun _ h => h.le
  -- the lower bounds of (21) tend to (i/l)^n e^((1 - i/l) a/b)
  have hP : ∀ i ∈ Finset.Ico 1 l, Tendsto (fun k => (N (jd i k) : ℝ) / N (m k) *
      Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b))) atTop
        (𝓝 (((i : ℝ) / l) ^ n * Real.exp ((1 - (i : ℝ) / l) * (a / b)))) := by
    intro i hi
    have hi0 : 0 < i := (Finset.mem_Ico.mp hi).1
    have hexp : Tendsto (fun k => Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b))) atTop
        (𝓝 (Real.exp ((1 - (i : ℝ) / l) * (a / b)))) :=
      (Real.continuous_exp.tendsto _).comp ((tendsto_const_nhds.sub
        ((auxiliaryDegree_ratio_tendsto i l hl0).comp hm)).mul_const _)
    exact (hilbert_auxiliary_ratio_tendsto n i l hi0 hl0 N hν hN m hm).mul hexp
  have hU : Tendsto (fun k => (D : ℝ) / t + D / m k) atTop (𝓝 ((D : ℝ) / t)) := by
    have h0 : Tendsto (fun k => (D : ℝ) / m k) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (D : ℝ)).comp hm
    simpa only [add_zero] using tendsto_const_nhds.add h0
  refine finite_grid_limit_contradiction n l hn hl
    (fun i k => (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k)
    (fun i k => (N (jd i k) : ℝ) / N (m k) * Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b)))
    (fun i k => Q k (jd i k) / Q k (m k)) (fun k => (D : ℝ) / t + D / m k) hD' hgap
    (fun i _ => hcoef i) hP hU ?_ ?_ ?_
  · exact (eventually_all_finset _).mpr fun i _ => hcoefpos i
  · intro η hη hη1
    refine (eventually_all_finset _).mpr fun i hi => ?_
    have hi0 : 0 < i := (Finset.mem_Ico.mp hi).1
    have hil : i ≤ l := (Finset.mem_Ico.mp hi).2.le
    have hq := (auxiliaryDegree_tendsto_atTop i l hi0 hl0).comp hm
    filter_upwards [positive_liminf_auxiliary_ratio f (fun k => jd i k) m hc hη hη1 hliminf hbdd
      hq hfm, hineq, hmpos] with k hfk hk hmk
    obtain ⟨-, hfr⟩ := hfk
    obtain ⟨hAk, -, -, -, -, h21⟩ := hk
    have hmk' : (0 : ℝ) < m k := by exact_mod_cast hmk
    have hjm : (jd i k : ℝ) / m k ≤ 1 := by
      rw [div_le_one hmk']
      exact_mod_cast auxiliaryDegree_le_self (m k) i l hil
    have hab : a / b ≤ A k / t := by
      have hA0 : 0 ≤ A k := ha.le.trans hAk
      calc a / b ≤ a / t := div_le_div_of_nonneg_left ha.le ht htb
        _ ≤ A k / t := div_le_div_of_nonneg_right hAk ht.le
    have hexp : Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b)) ≤
        Real.exp ((1 - (jd i k : ℝ) / m k) * A k / t) := by
      rw [mul_div_assoc]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab (by linarith))
    have hN0 : (0 : ℝ) ≤ (N (jd i k) : ℝ) / N (m k) := by positivity
    have hη0 : 0 ≤ 1 - η := by linarith
    calc (1 - η) * ((N (jd i k) : ℝ) / N (m k) *
          Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b)))
        = (N (jd i k) : ℝ) / N (m k) * (1 - η) *
          Real.exp ((1 - (jd i k : ℝ) / m k) * (a / b)) := by ring
      _ ≤ (N (jd i k) : ℝ) / N (m k) * (f (jd i k) / f (m k)) *
          Real.exp ((1 - (jd i k : ℝ) / m k) * A k / t) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hfr hN0) hexp (Real.exp_pos _).le
        exact mul_nonneg hN0 (hη0.trans hfr)
      _ ≤ Q k (jd i k) / Q k (m k) := h21 i hi
  · -- drop the first term of (20) and use (16)
    filter_upwards [hineq, hcoefpos 0] with k hk h0
    obtain ⟨-, hQ, hQm, h16, h20, -⟩ := hk
    have hsplit := Finset.sum_range_eq_add_Ico (fun i =>
      (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k * (Q k (jd i k) / Q k (m k))) hl0
    have hfirst : 0 ≤ (lam * ((jd (0 + 1) k - jd 0 k : ℕ) : ℝ) - C) / m k *
        (Q k (jd 0 k) / Q k (m k)) := mul_nonneg h0 (div_nonneg (hQ _) hQm.le)
    have h20' : (D : ℝ) * ∑ i ∈ Finset.range l,
        (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k * (Q k (jd i k) / Q k (m k)) ≤
          T k + D / m k := h20
    rw [hsplit] at h20'
    have h1 : (D : ℝ) * ∑ i ∈ Finset.Ico 1 l,
        (lam * ((jd (i + 1) k - jd i k : ℕ) : ℝ) - C) / m k * (Q k (jd i k) / Q k (m k)) ≤
          T k + D / m k := by
      nlinarith [mul_nonneg hD'.le hfirst]
    linarith

/-- The center dimension is eventually zero along the chosen degrees, given one finite partition
with the gap of (23). -/
theorem eventually_point_centers_of_gap (n l : ℕ) (hn : 0 < n) (hl : 2 ≤ l)
    {lam t b a : ℝ} (hlam : 0 < lam) (ht : 0 < t) (htb : t ≤ b) (ha : 0 < a)
    (hgap : 1 / t < lam * uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * (a / b))) l)
    (N : ℕ → ℕ) {ν : ℝ} (hν : 0 < ν)
    (hN : Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν))
    (f : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hliminf : liminf f atTop = c)
    (hbdd : IsBoundedUnder (· ≥ ·) atTop f)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hfm : Tendsto (fun k => f (m k)) atTop (𝓝 c))
    (C : ℕ → ℝ) (M₀ : ℕ → ℕ) (P : ℕ → ℕ → Prop)
    (hdata : ∀ k D, 0 < D → D ≤ n → P k D → M₀ D ≤ m k →
      ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities N f t lam (C D) a l (m k) D Q T A) :
    ∀ᶠ k in atTop, ∀ D, 0 < D → D ≤ n → ¬ P k D := by
  have hall : (∀ᶠ k in atTop, ∀ D ∈ Finset.Icc 1 n, ¬ P k D) ↔
      ∀ D ∈ Finset.Icc 1 n, ∀ᶠ k in atTop, ¬ P k D := eventually_all_finset _
  suffices h : ∀ D ∈ Finset.Icc 1 n, ∀ᶠ k in atTop, ¬ P k D by
    exact (hall.mpr h).mono fun k hk D hD hDn => hk D (Finset.mem_Icc.mpr ⟨hD, hDn⟩)
  intro D hDmem
  obtain ⟨hD, hDn⟩ := Finset.mem_Icc.mp hDmem
  by_contra hfr
  rw [Filter.not_eventually] at hfr
  simp only [not_not] at hfr
  -- a subsequence on which the center has dimension D
  obtain ⟨φ, hφ, hPφ⟩ := Filter.extraction_of_frequently_atTop hfr
  have hmφ : Tendsto (fun k => m (φ k)) atTop atTop := hm.comp hφ.tendsto_atTop
  have hdataφ : ∀ k, ∃ (Q : ℕ → ℝ) (T A : ℝ), M₀ D ≤ m (φ k) →
      CenterDegreeInequalities N f t lam (C D) a l (m (φ k)) D Q T A := by
    intro k
    by_cases hk : M₀ D ≤ m (φ k)
    · obtain ⟨Q, T, A, h⟩ := hdata (φ k) D hD hDn (hPφ k) hk
      exact ⟨Q, T, A, fun _ => h⟩
    · exact ⟨0, 0, 0, fun h => absurd h hk⟩
  choose Q T A hQTA using hdataφ
  exact moving_center_partition_contradiction n l D hn hl hD N hν hN f hc hliminf hbdd
    (fun k => m (φ k)) hmφ (hfm.comp hφ.tendsto_atTop) hlam ht htb ha hgap Q T A
    ((hmφ.eventually (eventually_ge_atTop (M₀ D))).mono fun k hk => hQTA k hk)

/-- (23): for the parameter t chosen in [t₀, b), every minimizing pair along the chosen degrees
eventually has a point center. -/
theorem exists_parameter_point_centers (n : ℕ) (hn : 0 < n) {a b lam t₀ : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hlam : lam * b = n + 1) (ht₀ : t₀ < b) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ l : ℕ, 2 ≤ l ∧
      ∀ (N : ℕ → ℕ) {ν : ℝ}, 0 < ν →
        Tendsto (fun j : ℕ => (N j : ℝ) / (j : ℝ) ^ n) atTop (𝓝 ν) →
      ∀ (f : ℕ → ℝ) {c : ℝ}, 0 < c → liminf f atTop = c → IsBoundedUnder (· ≥ ·) atTop f →
      ∀ (m : ℕ → ℕ), Tendsto m atTop atTop → Tendsto (fun k => f (m k)) atTop (𝓝 c) →
      ∀ (C : ℕ → ℝ) (M₀ : ℕ → ℕ) (P : ℕ → ℕ → Prop),
        (∀ k D, 0 < D → D ≤ n → P k D → M₀ D ≤ m k →
          ∃ (Q : ℕ → ℝ) (T A : ℝ), CenterDegreeInequalities N f t lam (C D) a l (m k) D Q T A) →
        ∀ᶠ k in atTop, ∀ D, 0 < D → D ≤ n → ¬ P k D := by
  obtain ⟨t, ht₀', ht, htb, l, hl, hgap⟩ := exists_parameter_finite_partition_gap n ha hb hlam ht₀
  have hlampos : 0 < lam := by
    by_contra h
    push Not at h
    have : lam * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hb.le
    have : (0 : ℝ) < n + 1 := by positivity
    linarith
  refine ⟨t, ht₀', ht, htb, l, hl, ?_⟩
  intro N ν hν hN f c hc hliminf hbdd m hm hfm C M₀ P hdata
  exact eventually_point_centers_of_gap n l hn hl hlampos ht htb.le ha hgap N hν hN f hc
    hliminf hbdd m hm hfm C M₀ P hdata

variable {K : Type*} [Field K] {r d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)] [∀ j, FiniteDimensional K (V j)]

/-- (20) for actual Taylor data at the uniform partition j_i = ⌊M i/l⌋, which satisfies the step
conditions once M ≥ l (H + h₀ + λ^(d+1)). -/
theorem taylor_uniform_partition_bound
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h x y, T (j + h) (μ j h x y) = T j x * T h y)
    (R : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K)
    (Z : Set ((Fin r ⊕ Fin (d + 1)) →₀ ℕ))
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → m.toSyn a < m.toSyn b)
    (htan : ∀ β, tangentExponent r β ∈ Z)
    (hcoef : ∀ j x β, MvPowerSeries.coeff (tangentExponent r β) (T j x) =
      MvPowerSeries.coeff β (R j x))
    (hzero : ∀ j x, ∀ a ∈ Z, (∃ i, a (Sum.inl i) ≠ 0) → MvPowerSeries.coeff a (T j x) = 0)
    (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin (d + 1)), ∃ (x : V h₀) (u : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K),
      MvPowerSeries.constantCoeff u ≠ 0 ∧
        T h₀ x = u * MvPowerSeries.monomial (tangentExponent r (∑ i ∈ s, Finsupp.single i 1)) 1)
    (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * Module.finrank K (LinearMap.range (R q)) : ℕ) : ℝ) ^
        ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (l M : ℕ) (hl : 0 < l) (hM : l * (H + h₀ + s ^ (d + 1)) ≤ M)
    (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hQM : 0 < weightedSliceCount (taylorExponentPoints m T) M w) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range l,
      (((s : ℝ) * (auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l : ℕ) -
        ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀)) / M) *
          (weightedSliceCount (taylorExponentPoints m T) (auxiliaryDegree M i l) w /
            weightedSliceCount (taylorExponentPoints m T) M w)) ≤
      weightedTangentialSum (taylorExponentPoints m T) M w /
          ((M : ℝ) * weightedSliceCount (taylorExponentPoints m T) M w) +
        (d + 1 : ℝ) / M := by
  have hstep : ∀ i, H + h₀ + s ^ (d + 1) ≤ auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l :=
    fun i => auxiliaryDegree_step_ge M i l _ hl hM
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      simp at hH
    · exact h
  have hMpos : 0 < M := lt_of_lt_of_le (Nat.mul_pos hl (by have := pow_pos hs (d + 1); omega)) hM
  refine taylor_partition_moment_bound_of_restriction m T μ hT R Z hZ htan hcoef hzero h₀ hprod
    s H hroot hH (fun i => auxiliaryDegree M i l) l M hMpos (auxiliaryDegree_monotone M l)
    (auxiliaryDegree_self M l hl) w hw (fun i _ => ?_) (fun i _ => ?_) hQM
  · have := hstep i
    omega
  · have h := hstep i
    have h' : ((H + h₀ + s ^ (d + 1) : ℕ) : ℝ) ≤
        ((auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    nlinarith [mul_le_mul_of_nonneg_left h' hs0]

end MixedFujita
