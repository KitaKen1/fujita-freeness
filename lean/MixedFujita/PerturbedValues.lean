/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SupportPerturbation
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
Actual minimum values of perturbed power-series weights, their right
derivatives, and a common positive perturbation radius for a fixed finite
family. The radius is not uniform over moving centers or unbounded degrees.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

theorem finite_common_positive_radius {ι : Type*} (E : Finset ι) (P : ι → ℝ → Prop)
    (hP : ∀ i ∈ E, ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → P i ε) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → ∀ i ∈ E, P i ε := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i E hi ih =>
    obtain ⟨δ, hδ, hE⟩ := ih (fun k hk => hP k (Finset.mem_insert_of_mem hk))
    obtain ⟨η, hη, hiP⟩ := hP i (Finset.mem_insert_self _ _)
    refine ⟨min δ η, lt_min hδ hη, ?_⟩
    intro ε hε hεδ k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      exact hiP ε hε (le_min_iff.mp hεδ).2
    · exact hE ε hε (le_min_iff.mp hεδ).1 k hk

variable {σ K : Type*} [Fintype σ] [Field K]

noncomputable def powerSeriesPerturbedValue (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (φ : MvPowerSeries σ K) (ε : ℝ) : ℝ := by
  classical
  exact if h : 0 ≤ ε ∧ φ ≠ 0 then
    perturbedExponentCost w v u ε
      (Classical.choose (exists_minimal_perturbedExponentCost m w v u hw h.1 h.2))
  else 0

theorem powerSeriesPerturbedValue_spec (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) {φ : MvPowerSeries σ K}
    (hφ : φ ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ q, MvPowerSeries.coeff q φ ≠ 0 ∧
      powerSeriesPerturbedValue m w v u hw φ ε = perturbedExponentCost w v u ε q ∧
      ∀ r, MvPowerSeries.coeff r φ ≠ 0 →
        perturbedExponentCost w v u ε q ≤ perturbedExponentCost w v u ε r := by
  classical
  let hmin := exists_minimal_perturbedExponentCost m w v u hw hε hφ
  have hq := Classical.choose_spec hmin
  refine ⟨Classical.choose hmin, hq.1, ?_, hq.2⟩
  simp only [powerSeriesPerturbedValue,
    dite_eq_left (show 0 ≤ ε ∧ φ ≠ 0 from ⟨hε, hφ⟩)]

omit [Fintype σ] in
theorem initialMonomial_series_ne_zero (m : MonomialOrder σ)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ} (hp : IsInitialMonomial m φ p) : φ ≠ 0 := by
  intro h
  exact hp.1 (by simp [h])

theorem powerSeriesPerturbedValue_zero (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    powerSeriesPerturbedValue m w v u hw φ 0 = realExponentWeight w p := by
  obtain ⟨q, hq, hval, hmin⟩ := powerSeriesPerturbedValue_spec m w v u hw
    (initialMonomial_series_ne_zero _ hp) (le_refl 0)
  rw [hval]
  have hupper := hmin p hp.1
  have hlower := initialMonomial_realWeight_min m w v hw hp hq
  simp only [perturbedExponentCost, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at *
  exact le_antisymm hupper hlower

theorem powerSeriesPerturbedValue_le_weight_of_coeff (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) {φ : MvPowerSeries σ K} {q : σ →₀ ℕ}
    (hq : MvPowerSeries.coeff q φ ≠ 0) :
    powerSeriesPerturbedValue m w v u hw φ 0 ≤ realExponentWeight w q := by
  have hφ : φ ≠ 0 := by
    intro h
    exact hq (by simp [h])
  obtain ⟨p, hp, hval, hmin⟩ := powerSeriesPerturbedValue_spec m w v u hw hφ (le_refl 0)
  rw [hval]
  simpa only [perturbedExponentCost, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero]
    using hmin q hq

theorem powerSeriesPerturbedValue_firstVariation_bounds
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε ≤ δ →
      (natExponentDegree v p : ℝ) ≤
        (powerSeriesPerturbedValue m w v u hw φ ε - realExponentWeight w p) / ε ∧
      (powerSeriesPerturbedValue m w v u hw φ ε - realExponentWeight w p) / ε ≤
        (natExponentDegree v p : ℝ) + ε * (natExponentDegree u p : ℝ) := by
  obtain ⟨δ, hδ, hbound⟩ := powerSeries_perturbation_firstVariation_bound m w v u hw hp
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨q, hq, hval, hmin⟩ := powerSeriesPerturbedValue_spec m w v u hw
    (initialMonomial_series_ne_zero _ hp) hε.le
  rw [hval]
  exact hbound ε hε hεδ q hq (hmin p hp.1)

theorem powerSeriesPerturbedValue_hasDerivWithinAt
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    {φ : MvPowerSeries σ K} {p : σ →₀ ℕ}
    (hp : IsInitialMonomial (weightedMonomialOrder m w v hw) φ p) :
    HasDerivWithinAt (powerSeriesPerturbedValue m w v u hw φ)
      (natExponentDegree v p : ℝ) (Set.Ioi 0) 0 := by
  obtain ⟨δ, hδ, hbound⟩ := powerSeriesPerturbedValue_firstVariation_bounds m w v u hw hp
  have hupper : Tendsto (fun ε : ℝ => (natExponentDegree v p : ℝ) +
      ε * (natExponentDegree u p : ℝ)) (𝓝[>] 0) (𝓝 (natExponentDegree v p : ℝ)) := by
    have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hv : Tendsto (fun _ : ℝ => (natExponentDegree v p : ℝ))
        (𝓝[>] 0) (𝓝 (natExponentDegree v p : ℝ)) := tendsto_const_nhds
    have hu : Tendsto (fun _ : ℝ => (natExponentDegree u p : ℝ))
        (𝓝[>] 0) (𝓝 (natExponentDegree u p : ℝ)) := tendsto_const_nhds
    simpa using hv.add (hid.mul hu)
  have hbounds : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (natExponentDegree v p : ℝ) ≤
        (powerSeriesPerturbedValue m w v u hw φ ε - realExponentWeight w p) / ε ∧
      (powerSeriesPerturbedValue m w v u hw φ ε - realExponentWeight w p) / ε ≤
        (natExponentDegree v p : ℝ) + ε * (natExponentDegree u p : ℝ) := by
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact hbound ε hε.1 hε.2.le
  have hlimit := tendsto_const_nhds.squeeze' hupper
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mpr
  have heq : slope (powerSeriesPerturbedValue m w v u hw φ) 0 =
      (fun ε => (powerSeriesPerturbedValue m w v u hw φ ε - realExponentWeight w p) / ε) := by
    funext ε
    rw [slope_def_field, sub_zero, powerSeriesPerturbedValue_zero m w v u hw hp]
  rw [heq]
  exact hlimit

theorem finite_family_powerSeriesPerturbedValue_bounds {ι : Type*} (E : Finset ι)
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hp : ∀ i ∈ E, IsInitialMonomial (weightedMonomialOrder m w v hw) (φ i) (p i)) :
    ∃ δ > 0, ∀ ε, 0 ≤ ε → ε ≤ δ → ∀ i ∈ E,
      realExponentWeight w (p i) + ε * (natExponentDegree v (p i) : ℝ) ≤
        powerSeriesPerturbedValue m w v u hw (φ i) ε ∧
      powerSeriesPerturbedValue m w v u hw (φ i) ε ≤
        realExponentWeight w (p i) + ε * (natExponentDegree v (p i) : ℝ) +
          ε ^ 2 * (natExponentDegree u (p i) : ℝ) := by
  apply finite_common_positive_radius
  intro i hi
  obtain ⟨δ, hδ, hbound⟩ := powerSeries_perturbation_sandwich m w v u hw (hp i hi)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  obtain ⟨q, hq, hval, hmin⟩ := powerSeriesPerturbedValue_spec m w v u hw
    (initialMonomial_series_ne_zero _ (hp i hi)) hε
  rw [hval]
  exact hbound ε hε hεδ q hq (hmin (p i) (hp i hi).1)

end MixedFujita
