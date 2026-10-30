/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FiniteDegree
public import MixedFujita.FiniteQuadrature
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.LiminfLimsup

/-!
The degree arithmetic and positive-liminf comparison in Section 4.
Hilbert growth, positivity of the geometric liminf, and the geometric
scaled-test inequality are still separate inputs.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

def auxiliaryDegree (m i l : ℕ) : ℕ := m * i / l

theorem auxiliaryDegree_ratio_bounds (m i l : ℕ) (hm : 0 < m) (hl : 0 < l) :
    (i : ℝ) / l - 1 / m ≤ (auxiliaryDegree m i l : ℝ) / m ∧
      (auxiliaryDegree m i l : ℝ) / m ≤ (i : ℝ) / l := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hl' : 0 < (l : ℝ) := by exact_mod_cast hl
  have hlo : auxiliaryDegree m i l * l ≤ m * i := Nat.div_mul_le_self _ _
  have hhi : m * i < (auxiliaryDegree m i l + 1) * l := by
    have he := Nat.div_add_mod' (m * i) l
    have hr := Nat.mod_lt (m * i) hl
    unfold auxiliaryDegree
    rw [Nat.add_mul, one_mul]
    omega
  have hlo' : (auxiliaryDegree m i l : ℝ) * l ≤ (m : ℝ) * i := by exact_mod_cast hlo
  have hhi' : (m : ℝ) * i < ((auxiliaryDegree m i l : ℝ) + 1) * l := by
    exact_mod_cast hhi
  constructor
  · apply (le_div_iff₀ hm').mpr
    rw [sub_mul, div_mul_cancel₀ 1 hm'.ne', div_mul_eq_mul_div, sub_le_iff_le_add]
    apply (div_le_iff₀ hl').mpr
    nlinarith
  · exact (div_le_div_iff₀ hm' hl').mpr (by nlinarith)

theorem auxiliaryDegree_ratio_tendsto (i l : ℕ) (hl : 0 < l) :
    Tendsto (fun m : ℕ => (auxiliaryDegree m i l : ℝ) / m) atTop (𝓝 ((i : ℝ) / l)) := by
  have hlo : Tendsto (fun m : ℕ => (i : ℝ) / l - 1 / m) atTop (𝓝 ((i : ℝ) / l)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbounds : ∀ᶠ m : ℕ in atTop,
      (i : ℝ) / l - 1 / m ≤ (auxiliaryDegree m i l : ℝ) / m ∧
      (auxiliaryDegree m i l : ℝ) / m ≤ (i : ℝ) / l := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    exact auxiliaryDegree_ratio_bounds m i l hm hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

theorem auxiliaryDegree_tendsto_atTop (i l : ℕ) (hi : 0 < i) (hl : 0 < l) :
    Tendsto (fun m : ℕ => auxiliaryDegree m i l) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (N * l)] with m hm
  unfold auxiliaryDegree
  apply (Nat.le_div_iff_mul_le hl).mpr
  exact hm.trans (Nat.le_mul_of_pos_right m hi)

/-- Floor division is monotone in the partition index. -/
theorem auxiliaryDegree_monotone (m l : ℕ) : Monotone (fun i => auxiliaryDegree m i l) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.mul_le_mul_left m hij)

theorem auxiliaryDegree_step_ratio_tendsto (i l : ℕ) (hl : 0 < l) :
    Tendsto (fun m : ℕ =>
      ((auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l : ℕ) : ℝ) / m)
      atTop (𝓝 (1 / (l : ℝ))) := by
  have h := (auxiliaryDegree_ratio_tendsto (i + 1) l hl).sub
    (auxiliaryDegree_ratio_tendsto i l hl)
  have heq : (fun m : ℕ =>
      ((auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l : ℕ) : ℝ) / m) =
      (fun m : ℕ => (auxiliaryDegree m (i + 1) l : ℝ) / m -
        (auxiliaryDegree m i l : ℝ) / m) := by
    funext m
    rw [Nat.cast_sub (auxiliaryDegree_monotone m l (Nat.le_succ i)), sub_div]
  rw [heq]
  have hc : ((i + 1 : ℕ) : ℝ) / l - (i : ℝ) / l = 1 / l := by push_cast; ring
  simpa only [hc] using h

/-- The fixed error C disappears, while the leading increment tends to lam/l. -/
theorem adjusted_auxiliary_step_tendsto (i l : ℕ) (hl : 0 < l) (lam C : ℝ) :
    Tendsto (fun m : ℕ =>
      (lam * ((auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l : ℕ) : ℝ) - C) / m)
      atTop (𝓝 (lam / l)) := by
  have h := ((auxiliaryDegree_step_ratio_tendsto i l hl).const_mul lam).sub
    (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C)
  have heq : (fun m : ℕ =>
      (lam * ((auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l : ℕ) : ℝ) - C) / m) =
      (fun m : ℕ => lam *
        (((auxiliaryDegree m (i + 1) l - auxiliaryDegree m i l : ℕ) : ℝ) / m) - C / m) := by
    funext m
    ring
  rw [heq]
  simpa only [sub_zero, mul_one_div] using h

/-- Uniformly in any auxiliary index tending to infinity, f_j/f_m is eventually
at least 1-eta along a positive-liminf degree sequence. -/
theorem positive_liminf_auxiliary_ratio (f : ℕ → ℝ) (q m : ℕ → ℕ) {c η : ℝ}
    (hc : 0 < c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hliminf : liminf f atTop = c)
    (hbounded : IsBoundedUnder (· ≥ ·) atTop f)
    (hq : Tendsto q atTop atTop)
    (hfm : Tendsto (fun k => f (m k)) atTop (𝓝 c)) :
    ∀ᶠ k in atTop, 0 < f (m k) ∧ 1 - η ≤ f (q k) / f (m k) := by
  let δ : ℝ := c * η / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4 * δ = c * η := by dsimp [δ]; ring
  have hqlo : ∀ᶠ k in atTop, c - δ < f (q k) := by
    have hbase : ∀ᶠ j in atTop, c - δ < f j := by
      apply eventually_lt_of_lt_liminf _ hbounded
      rw [hliminf]
      linarith
    exact hq.eventually hbase
  have hmhi : ∀ᶠ k in atTop, f (m k) < c + δ :=
    hfm.eventually (gt_mem_nhds (by linarith))
  have hmpos : ∀ᶠ k in atTop, 0 < f (m k) := hfm.eventually (lt_mem_nhds hc)
  filter_upwards [hqlo, hmhi, hmpos] with k hqk hmk hmkpos
  refine ⟨hmkpos, (le_div_iff₀ hmkpos).mpr ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hmk.le (sub_nonneg.mpr hη1)
  have hηδ := mul_nonneg hη.le hδ.le
  nlinarith

/-- Finite sums pass to the degree limit even when a ratio has only lower
envelopes (1-eta)*P. Eta is removed with the explicit sequence 1/(n+1). -/
theorem finite_partition_limit_bound {ι : Type*} (E : Finset ι)
    (a P Qratio : ι → ℕ → ℝ) (α ρ : ι → ℝ) (U : ℕ → ℝ) {D u : ℝ}
    (hD : 0 ≤ D)
    (ha : ∀ i ∈ E, Tendsto (a i) atTop (𝓝 (α i)))
    (hP : ∀ i ∈ E, Tendsto (P i) atTop (𝓝 (ρ i)))
    (hU : Tendsto U atTop (𝓝 u))
    (hanonneg : ∀ᶠ k in atTop, ∀ i ∈ E, 0 ≤ a i k)
    (hratio : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ k in atTop, ∀ i ∈ E, (1 - η) * P i k ≤ Qratio i k)
    (hbound : ∀ᶠ k in atTop, D * (∑ i ∈ E, a i k * Qratio i k) ≤ U k) :
    D * (∑ i ∈ E, α i * ρ i) ≤ u := by
  have hηbound (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
      (1 - η) * (D * (∑ i ∈ E, α i * ρ i)) ≤ u := by
    have hsum := (tendsto_finsetSum E (fun i hi =>
      (ha i hi).mul ((hP i hi).const_mul (1 - η)))).const_mul D
    have hev : ∀ᶠ k in atTop,
        D * (∑ i ∈ E, a i k * ((1 - η) * P i k)) ≤ U k := by
      filter_upwards [hanonneg, hratio η hη hη1, hbound] with k hAk hRk hBk
      apply le_trans _ hBk
      apply mul_le_mul_of_nonneg_left _ hD
      exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hRk i hi) (hAk i hi)
    have hlim := le_of_tendsto_of_tendsto hsum hU hev
    have heq : D * (∑ i ∈ E, α i * ((1 - η) * ρ i)) =
        (1 - η) * (D * (∑ i ∈ E, α i * ρ i)) := by
      calc
        _ = D * ((1 - η) * (∑ i ∈ E, α i * ρ i)) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by ring
    rwa [heq] at hlim
  have hlim : Tendsto (fun n : ℕ =>
      (1 - 1 / ((n : ℝ) + 1)) * (D * (∑ i ∈ E, α i * ρ i))) atTop
      (𝓝 (D * (∑ i ∈ E, α i * ρ i))) := by
    simpa only [sub_zero, one_mul] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const
          (D * (∑ i ∈ E, α i * ρ i))
  exact le_of_tendsto' hlim fun n => hηbound (1 / ((n : ℝ) + 1))
    (by positivity) ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n]))

/-- Close the analytic contradiction at one fixed partition. These inputs are
precisely degree convergence, lower ratio envelopes, and the finite moment
upper bound; their geometric construction is not asserted here. -/
theorem finite_grid_limit_contradiction (n l : ℕ) (hn : 0 < n) (hl : 2 ≤ l)
    (a P Qratio : ℕ → ℕ → ℝ) (U : ℕ → ℝ) {D lam c t : ℝ}
    (hD : 0 < D)
    (hgap : 1 / t < lam * uniformGridSum
      (fun s => s ^ n * Real.exp ((1 - s) * c)) l)
    (ha : ∀ i ∈ Finset.Ico 1 l, Tendsto (a i) atTop (𝓝 (lam / l)))
    (hP : ∀ i ∈ Finset.Ico 1 l, Tendsto (P i) atTop
      (𝓝 (((i : ℝ) / l) ^ n * Real.exp ((1 - (i : ℝ) / l) * c))))
    (hU : Tendsto U atTop (𝓝 (D / t)))
    (hanonneg : ∀ᶠ k in atTop, ∀ i ∈ Finset.Ico 1 l, 0 ≤ a i k)
    (hratio : ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ k in atTop, ∀ i ∈ Finset.Ico 1 l, (1 - η) * P i k ≤ Qratio i k)
    (hbound : ∀ᶠ k in atTop, D * (∑ i ∈ Finset.Ico 1 l, a i k * Qratio i k) ≤ U k) :
    False := by
  have hlim := finite_partition_limit_bound (Finset.Ico 1 l) a P Qratio
    (fun _ => lam / l)
    (fun i => ((i : ℝ) / l) ^ n * Real.exp ((1 - (i : ℝ) / l) * c)) U
    hD.le ha hP hU hanonneg hratio hbound
  have heq : D * (∑ i ∈ Finset.Ico 1 l,
      (lam / l) * (((i : ℝ) / l) ^ n * Real.exp ((1 - (i : ℝ) / l) * c))) =
      D * (lam * uniformGridSum (fun s => s ^ n * Real.exp ((1 - s) * c)) l) := by
    rw [exponential_uniformGridSum_eq_interior n l hn (by omega) c, ← Finset.mul_sum]
    ring
  rw [heq] at hlim
  have hstrict := mul_lt_mul_of_pos_left hgap hD
  rw [mul_one_div] at hstrict
  exact (not_lt_of_ge hlim) hstrict

end MixedFujita
