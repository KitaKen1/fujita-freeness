/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityStability
public import MixedFujita.DegreeLimits
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Analysis.Normed.Group.Constructions

/-!
Explicit rational boxes inside the positive simplex. Their lattice counts
have positive limiting density. Equality in the limiting moment therefore
forces every such box to meet the exponent set. The hypotheses are numerical
Hilbert and moment convergence, not geometric section-space constructions.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

/-- A translated integer cube with width floor(m*b/q). -/
def rationalLatticeBox {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun i => Finset.Ico (auxiliaryDegree m (a i) q)
    (auxiliaryDegree m (a i) q + auxiliaryDegree m b q))

theorem rationalLatticeBox_mem {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ) (γ : Fin n → ℕ) :
    γ ∈ rationalLatticeBox a b q m ↔ ∀ i,
      auxiliaryDegree m (a i) q ≤ γ i ∧
        γ i < auxiliaryDegree m (a i) q + auxiliaryDegree m b q := by
  simp only [rationalLatticeBox, Fintype.mem_piFinset, Finset.mem_Ico]

theorem rationalLatticeBox_card {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ) :
    (rationalLatticeBox a b q m).card = auxiliaryDegree m b q ^ n := by
  simp [rationalLatticeBox, Fintype.card_piFinset]

theorem rationalLatticeBox_normalizedCard {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ) :
    normalizedLatticeCard (rationalLatticeBox a b q m) m =
      ((auxiliaryDegree m b q : ℝ) / m) ^ n := by
  rw [normalizedLatticeCard, rationalLatticeBox_card, Nat.cast_pow, div_pow]

theorem rationalLatticeBox_card_tendsto {n : ℕ} (a : Fin n → ℕ) (b q : ℕ)
    (hq : 0 < q) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    Tendsto (fun k => normalizedLatticeCard (rationalLatticeBox a b q (m k)) (m k))
      atTop (𝓝 (((b : ℝ) / q) ^ n)) := by
  simp only [rationalLatticeBox_normalizedCard]
  exact ((auxiliaryDegree_ratio_tendsto b q hq).comp hm).pow n

theorem rationalLatticeBox_coordinate_bounds {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ)
    (hq : 0 < q) (hm : 0 < m) {γ : Fin n → ℕ}
    (hγ : γ ∈ rationalLatticeBox a b q m) (i : Fin n) :
    (a i : ℝ) / q - 1 / m ≤ (γ i : ℝ) / m ∧
      (γ i : ℝ) / m ≤ ((a i : ℝ) + b) / q := by
  have hi := (rationalLatticeBox_mem a b q m γ).mp hγ i
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  refine ⟨(auxiliaryDegree_ratio_bounds m (a i) q hm hq).1.trans ?_, ?_⟩
  · apply div_le_div_of_nonneg_right _ hm'.le
    exact_mod_cast hi.1
  · have hup : (γ i : ℝ) ≤ (auxiliaryDegree m (a i) q : ℝ) + auxiliaryDegree m b q := by
      exact_mod_cast hi.2.le
    have hratio := div_le_div_of_nonneg_right hup hm'.le
    rw [add_div] at hratio
    have h1 := (auxiliaryDegree_ratio_bounds m (a i) q hm hq).2
    have h2 := (auxiliaryDegree_ratio_bounds m b q hm hq).2
    rw [add_div]
    linarith

theorem rationalLatticeBox_degree_bound {n : ℕ} (a : Fin n → ℕ) (b q m : ℕ)
    (hq : 0 < q) (hm : 0 < m) {γ : Fin n → ℕ}
    (hγ : γ ∈ rationalLatticeBox a b q m) :
    (∑ i, (γ i : ℝ)) ≤
      ((∑ i, (a i : ℝ)) + (n : ℝ) * b) / q * m := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => (rationalLatticeBox_coordinate_bounds a b q m hq hm hγ i).2)
  have heq : (∑ i, ((a i : ℝ) + b) / (q : ℝ)) =
      ((∑ i, (a i : ℝ)) + (n : ℝ) * b) / q := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    simp
  rw [← Finset.sum_div, heq] at hsum
  exact (div_le_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)).mp hsum

/-- Every fixed rational box strictly inside the simplex eventually meets E.
Omitted points in the box have zero limiting density, whereas the box has
positive density (b/q)^n. -/
theorem equality_mean_eventually_meets_rational_box {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (a : Fin n → ℕ) (b q : ℕ)
    (hm : Tendsto m atTop atTop) (hb : 0 < b) (hq : 0 < q) {C : ℝ} (hC : 0 < C)
    (hroom : ((∑ i, (a i : ℝ)) + (n : ℝ) * b) / q < C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, (E k ∩ rationalLatticeBox a b q (m k)).Nonempty := by
  let A : ℝ := ((∑ i, (a i : ℝ)) + (n : ℝ) * b) / q
  let ε : ℝ := (C - A) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let F : ℕ → Finset (Fin n → ℕ) := fun k => rationalLatticeBox a b q (m k) \ E k
  have hsmall : Tendsto (fun k => (n : ℝ) / m k) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) n).comp hm
  have hmpos : ∀ᶠ k in atTop, 0 < m k := hm.eventually (eventually_gt_atTop 0)
  have hcost : ∀ᶠ k in atTop, ∀ γ ∈ F k,
      (((∑ i, γ i) + n : ℕ) : ℝ) ≤ (C - ε) * m k := by
    filter_upwards [hmpos, hsmall.eventually (gt_mem_nhds hε)] with k hmk hnk γ hγ
    have hγbox := Finset.mem_sdiff.mp hγ |>.1
    have hdeg := rationalLatticeBox_degree_bound a b q (m k) hq hmk hγbox
    have hn := (div_le_iff₀ (by exact_mod_cast hmk : (0 : ℝ) < m k)).mp hnk.le
    dsimp only [ε] at hn
    simp only [Nat.cast_add, Nat.cast_sum]
    dsimp only [ε]
    change (∑ i, (γ i : ℝ)) + n ≤ (C - (C - A) / 2) * m k
    change (∑ i, (γ i : ℝ)) ≤ A * m k at hdeg
    nlinarith
  have hF := lattice_missing_mass_tendsto_zero E F m hm hC hε
    (fun _ => Finset.disjoint_sdiff) hcost hcard hmean
  have hB := rationalLatticeBox_card_tendsto a b q hq m hm
  have hvol : 0 < ((b : ℝ) / q) ^ n := by positivity
  filter_upwards [hF.eventually (gt_mem_nhds (half_pos hvol)),
    hB.eventually (lt_mem_nhds (show ((b : ℝ) / q) ^ n / 2 < ((b : ℝ) / q) ^ n by linarith))]
    with k hFk hBk
  by_contra hinter
  have hdisj : Disjoint (rationalLatticeBox a b q (m k)) (E k) := by
    apply Disjoint.symm
    apply Finset.disjoint_iff_inter_eq_empty.mpr
    exact Finset.not_nonempty_iff_eq_empty.mp hinter
  have heq : F k = rationalLatticeBox a b q (m k) := Finset.sdiff_eq_self_iff_disjoint.mpr hdisj
  rw [heq] at hFk
  linarith

/-- The equality-case density statement: every positive point strictly inside
the simplex is eventually approximated, in every coordinate, by an exponent.
This is enough to meet every fixed open ball in the simplex interior. -/
theorem equality_mean_eventually_approximates_interior {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (u : Fin n → ℝ)
    {C r : ℝ} (hm : Tendsto m atTop atTop) (hC : 0 < C) (hr : 0 < r)
    (hu : ∀ i, 0 < u i) (hsum : (∑ i, u i) < C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, ∃ γ ∈ E k, ∀ i, |(γ i : ℝ) / m k - u i| < r := by
  have hmargin : 0 < C - ∑ i, u i := sub_pos.mpr hsum
  obtain ⟨q, hq⟩ := exists_nat_gt (max 1 (max ((n : ℝ) / (C - ∑ i, u i)) (2 / r)))
  have hq1 : (1 : ℝ) < q := (le_max_left _ _).trans_lt hq
  have hqpos : 0 < q := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hq1)
  have hqr : 0 < (q : ℝ) := by exact_mod_cast hqpos
  have hwide : (n : ℝ) / q < C - ∑ i, u i := by
    have hstrict : (n : ℝ) / (C - ∑ i, u i) < q :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hq)
    have hmul := (div_lt_iff₀ hmargin).mp hstrict
    exact (div_lt_iff₀ hqr).mpr (by nlinarith)
  have hclose : 2 / (q : ℝ) < r := by
    have h : 2 / r < q := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hq)
    have hmul := (div_lt_iff₀ hr).mp h
    exact (div_lt_iff₀ hqr).mpr (by nlinarith)
  have hclose' : 1 / (q : ℝ) + 1 / q < r := by
    have heq : 2 / (q : ℝ) = 1 / q + 1 / q := by ring
    rwa [heq] at hclose
  let a : Fin n → ℕ := fun i => ⌊(q : ℝ) * u i⌋₊
  have ha (i : Fin n) : (a i : ℝ) / q ≤ u i := by
    apply (div_le_iff₀ hqr).mpr
    dsimp [a]
    simpa only [mul_comm] using Nat.floor_le (mul_nonneg hqr.le (hu i).le)
  have hb (i : Fin n) : u i < ((a i : ℝ) + 1) / q := by
    apply (lt_div_iff₀ hqr).mpr
    simpa only [a, mul_comm] using Nat.lt_floor_add_one ((q : ℝ) * u i)
  have hroom : ((∑ i, (a i : ℝ)) + (n : ℝ) * (1 : ℕ)) / q < C := by
    have hsumA := Finset.sum_le_sum (s := Finset.univ) (fun i _ => ha i)
    rw [← Finset.sum_div] at hsumA
    simp only [Nat.cast_one, mul_one, add_div]
    linarith
  have hmeet := equality_mean_eventually_meets_rational_box E m a 1 q hm
    (by decide) hqpos hC hroom hcard hmean
  filter_upwards [hmeet, hm.eventually (eventually_ge_atTop q)] with k hk hmk
  obtain ⟨γ, hγ⟩ := hk
  have hγE := (Finset.mem_inter.mp hγ).1
  have hγB := (Finset.mem_inter.mp hγ).2
  have hmkpos : 0 < m k := hqpos.trans_le hmk
  have hrecip : 1 / (m k : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqr (by exact_mod_cast hmk)
  refine ⟨γ, hγE, ?_⟩
  intro i
  obtain ⟨hlo, hhi⟩ := rationalLatticeBox_coordinate_bounds a 1 q (m k) hqpos hmkpos hγB i
  have hai := ha i
  have hbi := hb i
  simp only [Nat.cast_one, add_div] at hhi hbi
  apply abs_lt.mpr
  constructor <;> linarith

theorem equality_mean_eventually_meets_ball {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (u : Fin n → ℝ)
    {C r : ℝ} (hm : Tendsto m atTop atTop) (hC : 0 < C) (hr : 0 < r)
    (hu : ∀ i, 0 < u i) (hsum : (∑ i, u i) < C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, ∃ γ ∈ E k, (fun i => (γ i : ℝ) / m k) ∈ Metric.ball u r := by
  filter_upwards [equality_mean_eventually_approximates_interior E m u hm hC hr hu hsum
    hcard hmean] with k hk
  obtain ⟨γ, hγ, happ⟩ := hk
  refine ⟨γ, hγ, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr]
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using happ i

/-- Select all finitely many approximation targets in the same large degree. -/
theorem equality_mean_eventually_approximates_finite_family {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (U : Finset (Fin n → ℝ))
    {C r : ℝ} (hm : Tendsto m atTop atTop) (hC : 0 < C) (hr : 0 < r)
    (hu : ∀ u ∈ U, ∀ i, 0 < u i) (hsum : ∀ u ∈ U, (∑ i, u i) < C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, ∀ u ∈ U, ∃ γ ∈ E k, ∀ i, |(γ i : ℝ) / m k - u i| < r := by
  exact U.eventually_all.mpr fun u huU => equality_mean_eventually_approximates_interior
    E m u hm hC hr (hu u huU) (hsum u huU) hcard hmean

end MixedFujita
