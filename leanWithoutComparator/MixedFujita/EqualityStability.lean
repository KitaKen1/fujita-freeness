/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SimplexMoment
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
Stability of the lattice moment bound in the smooth volume equality case.
Insert omitted low-cost lattice points into a disjoint union and apply the
already proved moment bound once. The omitted points force an explicit
positive penalty; no sorted minimizer or rearrangement theorem is needed.
Geometric Hilbert growth and the subsequent threshold/lifting argument
remain separate unfinished dependencies.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

/-- Insert the omitted set F, bound its cost from above, and subtract it. -/
theorem finite_missing_cost_penalty {ι : Type*} [DecidableEq ι]
    (E F : Finset ι) (c : ι → ℝ) (n : ℕ) (hEF : Disjoint E F)
    (hc : ∀ i ∈ E ∪ F, 0 ≤ c i)
    (hcount : ∀ t ≥ 0, cumulativeCount (E ∪ F) c t ≤ t ^ n / (n.factorial : ℝ))
    {R U : ℝ} (hR : 0 ≤ R) (hF : ∀ i ∈ F, c i ≤ U) :
    R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) +
      (R - U) * (F.card : ℝ) ≤ ∑ i ∈ E, c i := by
  have h := finite_moment_lower_bound_of_count (E ∪ F) c n hc hcount hR
  rw [Finset.card_union_of_disjoint hEF, Finset.sum_union hEF, Nat.cast_add] at h
  have hcost : (∑ i ∈ F, c i) ≤ U * (F.card : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ F, U := Finset.sum_le_sum hF
      _ = _ := by simp [mul_comm]
  linarith

noncomputable def latticeDegreeSum {n : ℕ} (E : Finset (Fin n → ℕ)) : ℝ :=
  ∑ γ ∈ E, (∑ i, (γ i : ℝ))

theorem lattice_cost_sum_eq_degreeSum {n : ℕ} (E : Finset (Fin n → ℕ)) :
    (∑ γ ∈ E, (((∑ i, γ i) + n : ℕ) : ℝ)) =
      latticeDegreeSum E + (n : ℝ) * (E.card : ℝ) := by
  simp only [Nat.cast_add, Nat.cast_sum, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, latticeDegreeSum]
  ring

/-- Missing lattice points below R-epsilon cost epsilon per missing point. -/
theorem lattice_missing_moment_penalty {n : ℕ} (E F : Finset (Fin n → ℕ))
    (hEF : Disjoint E F) {R U : ℝ} (hR : 0 ≤ R)
    (hF : ∀ γ ∈ F, (((∑ i, γ i) + n : ℕ) : ℝ) ≤ U) :
    R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) +
      (R - U) * (F.card : ℝ) ≤ latticeDegreeSum E + (n : ℝ) * (E.card : ℝ) := by
  have h := finite_missing_cost_penalty E F
    (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ)) n hEF
    (fun _ _ => by positivity) (fun _ ht => lattice_cumulativeCount_bound n (E ∪ F) ht) hR hF
  rwa [lattice_cost_sum_eq_degreeSum] at h

noncomputable def normalizedLatticeCard {n : ℕ} (E : Finset (Fin n → ℕ)) (m : ℝ) : ℝ :=
  (E.card : ℝ) / m ^ n

noncomputable def normalizedLatticeMean {n : ℕ} (E : Finset (Fin n → ℕ)) (m : ℝ) : ℝ :=
  latticeDegreeSum E / (m * (E.card : ℝ))

/-- Homogeneous form of the finite penalty, suitable for Hilbert asymptotics. -/
theorem normalized_lattice_missing_penalty {n : ℕ} (E F : Finset (Fin n → ℕ))
    (hEF : Disjoint E F) (hE : E.Nonempty) {m C ε : ℝ}
    (hm : 0 < m) (hC : 0 ≤ C)
    (hF : ∀ γ ∈ F, (((∑ i, γ i) + n : ℕ) : ℝ) ≤ (C - ε) * m) :
    ε * normalizedLatticeCard F m ≤
      normalizedLatticeCard E m * (normalizedLatticeMean E m + (n : ℝ) / m - C) +
        C ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
  have h := lattice_missing_moment_penalty E F hEF (mul_nonneg hC hm.le) hF
  have hcard : (E.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hE).ne'
  have hden : (n + 1 : ℝ) * (n.factorial : ℝ) ≠ 0 := by positivity
  have heqL : m ^ (n + 1) * (ε * normalizedLatticeCard F m) =
      ε * m * (F.card : ℝ) := by
    unfold normalizedLatticeCard
    rw [pow_succ]
    field_simp
  have heqR : m ^ (n + 1) *
      (normalizedLatticeCard E m * (normalizedLatticeMean E m + (n : ℝ) / m - C) +
        C ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ))) =
      latticeDegreeSum E + (n : ℝ) * (E.card : ℝ) - C * m * (E.card : ℝ) +
        (C * m) ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
    unfold normalizedLatticeCard normalizedLatticeMean
    rw [mul_pow, pow_succ]
    field_simp
  apply (mul_le_mul_iff_right₀ (pow_pos hm (n + 1))).mp
  rw [heqL, heqR]
  nlinarith

/-- At the minimum limiting mean, omitted points uniformly below the simplex
boundary have vanishing normalized cardinality. Hilbert and mean convergence
are numerical inputs, with no claim that geometric sections supply them yet. -/
theorem lattice_missing_mass_tendsto_zero {n : ℕ}
    (E F : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) {C ε : ℝ}
    (hm : Tendsto m atTop atTop) (hC : 0 < C) (hε : 0 < ε)
    (hEF : ∀ k, Disjoint (E k) (F k))
    (hcost : ∀ᶠ k in atTop, ∀ γ ∈ F k,
      (((∑ i, γ i) + n : ℕ) : ℝ) ≤ (C - ε) * m k)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    Tendsto (fun k => normalizedLatticeCard (F k) (m k)) atTop (𝓝 0) := by
  have hE : ∀ᶠ k in atTop, (E k).Nonempty := by
    have hp : 0 < C ^ n / (n.factorial : ℝ) := by positivity
    filter_upwards [hcard.eventually (lt_mem_nhds hp)] with k hk
    by_contra he
    have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hempty, normalizedLatticeCard, Finset.card_empty, Nat.cast_zero, zero_div] at hk
    exact (lt_irrefl 0) hk
  have hmpos : ∀ᶠ k in atTop, 0 < m k := hm.eventually (eventually_gt_atTop 0)
  have hsmall : Tendsto (fun k => (n : ℝ) / m k) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) n).comp hm
  let G : ℕ → ℝ := fun k =>
    normalizedLatticeCard (E k) (m k) *
      (normalizedLatticeMean (E k) (m k) + (n : ℝ) / m k - C) +
        C ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ))
  have hcancel : C ^ n / (n.factorial : ℝ) *
      ((n : ℝ) / (n + 1 : ℝ) * C + 0 - C) +
        C ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) = 0 := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    ring
  have hG : Tendsto G atTop (𝓝 0) := by
    have h := (hcard.mul ((hmean.add hsmall).sub (tendsto_const_nhds (x := C)))).add
      (tendsto_const_nhds (x := C ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ))))
    simpa only [hcancel] using h
  have hupper : ∀ᶠ k in atTop, normalizedLatticeCard (F k) (m k) ≤ G k / ε := by
    filter_upwards [hmpos, hE, hcost] with k hmk hEk hFk
    have h := normalized_lattice_missing_penalty (E k) (F k) (hEF k) hEk
      (by exact_mod_cast hmk) hC.le hFk
    apply (le_div_iff₀ hε).mpr
    dsimp only [G]
    simpa only [mul_comm] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_div] using hG.div_const ε)
    (Eventually.of_forall fun _ => by unfold normalizedLatticeCard; positivity) hupper

end MixedFujita
