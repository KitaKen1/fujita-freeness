/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PerturbedValues
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
The finite exponential objective in Section 4. A right local minimum implies
the weighted tangential moment bound. For actual MvPowerSeries, the value
derivatives are supplied by PerturbedValues; geometric specialization and
minimality still have to supply the local-minimum hypothesis.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

noncomputable def sectionExponentialObjective {ι : Type*} (E : Finset ι) (t j : ℝ)
    (A : ℝ → ℝ) (μ : ι → ℝ → ℝ) (ε : ℝ) : ℝ :=
  (∑ i ∈ E, Real.exp (A ε / t - μ i ε / j)) / (E.card : ℝ)

noncomputable def sectionExponentialWeightSum {ι : Type*} (E : Finset ι)
    (l : ι → ℝ) (j : ℝ) : ℝ := ∑ i ∈ E, Real.exp (-l i / j)

noncomputable def sectionExponentialMoment {ι : Type*} (E : Finset ι)
    (l b : ι → ℝ) (j : ℝ) : ℝ :=
  (∑ i ∈ E, b i * Real.exp (-l i / j)) / (j * sectionExponentialWeightSum E l j)

theorem sectionExponentialObjective_factor {ι : Type*} (E : Finset ι) (t j : ℝ)
    (A : ℝ → ℝ) (μ : ι → ℝ → ℝ) (ε : ℝ) :
    sectionExponentialObjective E t j A μ ε =
      Real.exp (A ε / t) / (E.card : ℝ) * sectionExponentialWeightSum E (fun i => μ i ε) j := by
  have hsum : (∑ i ∈ E, Real.exp (A ε / t - μ i ε / j)) =
      Real.exp (A ε / t) * ∑ i ∈ E, Real.exp (-μ i ε / j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sub_eq_add_neg, Real.exp_add, neg_div]
  unfold sectionExponentialObjective sectionExponentialWeightSum
  rw [hsum]
  ring

theorem sectionExponentialWeightSum_pos {ι : Type*} (E : Finset ι)
    (l : ι → ℝ) (j : ℝ) (hE : E.Nonempty) : 0 < sectionExponentialWeightSum E l j := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) hE

theorem sectionExponentialObjective_hasDerivWithinAt {ι : Type*}
    (E : Finset ι) (t j : ℝ) (A : ℝ → ℝ) (μ : ι → ℝ → ℝ) (d : ℝ) (b : ι → ℝ)
    (hA : HasDerivWithinAt A d (Set.Ioi 0) 0)
    (hμ : ∀ i ∈ E, HasDerivWithinAt (μ i) (b i) (Set.Ioi 0) 0) :
    HasDerivWithinAt (sectionExponentialObjective E t j A μ)
      ((∑ i ∈ E, Real.exp (A 0 / t - μ i 0 / j) * (d / t - b i / j)) /
        (E.card : ℝ)) (Set.Ioi 0) 0 := by
  exact (HasDerivWithinAt.fun_sum (fun i hi =>
    ((hA.div_const t).sub ((hμ i hi).div_const j)).exp)).div_const (E.card : ℝ)

theorem exponentialObjective_derivative_factor {ι : Type*}
    (E : Finset ι) (l b : ι → ℝ) (A d t j : ℝ) :
    (∑ i ∈ E, Real.exp (A / t - l i / j) * (d / t - b i / j)) / (E.card : ℝ) =
      Real.exp (A / t) / (E.card : ℝ) *
        ((d / t) * sectionExponentialWeightSum E l j -
          (∑ i ∈ E, b i * Real.exp (-l i / j)) / j) := by
  have hsum : (∑ i ∈ E, Real.exp (A / t - l i / j) * (d / t - b i / j)) =
      Real.exp (A / t) *
        ((d / t) * sectionExponentialWeightSum E l j -
          (∑ i ∈ E, b i * Real.exp (-l i / j)) / j) := by
    calc
      _ = Real.exp (A / t) *
          (∑ i ∈ E, ((d / t) * Real.exp (-l i / j) -
            (b i * Real.exp (-l i / j)) / j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [sub_eq_add_neg, Real.exp_add]
        simp only [neg_div]
        ring
      _ = _ := by
        simp only [div_eq_mul_inv, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_mul, sectionExponentialWeightSum]
  rw [hsum]
  ring

theorem right_derivative_nonneg_of_minimum {F : ℝ → ℝ} {D : ℝ}
    (hF : HasDerivWithinAt F D (Set.Ioi 0) 0)
    (hmin : ∀ᶠ ε : ℝ in 𝓝[>] 0, F 0 ≤ F ε) : 0 ≤ D := by
  have hlimit := (hasDerivWithinAt_iff_tendsto_slope'
    (by simp : (0 : ℝ) ∉ Set.Ioi 0)).mp hF
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin, hmin] with ε hε hεmin
  rw [slope_def_field, sub_zero]
  exact div_nonneg (sub_nonneg.mpr hεmin) hε.le

theorem exponential_moment_upper_bound_of_minimum {ι : Type*}
    (E : Finset ι) (hE : E.Nonempty) (t j : ℝ) (hj : 0 < j)
    (A : ℝ → ℝ) (μ : ι → ℝ → ℝ) (d : ℝ) (b : ι → ℝ)
    (hA : HasDerivWithinAt A d (Set.Ioi 0) 0)
    (hμ : ∀ i ∈ E, HasDerivWithinAt (μ i) (b i) (Set.Ioi 0) 0)
    (hmin : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      sectionExponentialObjective E t j A μ 0 ≤ sectionExponentialObjective E t j A μ ε) :
    sectionExponentialMoment E (fun i => μ i 0) b j ≤ d / t := by
  have hD := right_derivative_nonneg_of_minimum
    (sectionExponentialObjective_hasDerivWithinAt E t j A μ d b hA hμ) hmin
  rw [exponentialObjective_derivative_factor] at hD
  have hcard : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
  have hfactor : 0 < Real.exp (A 0 / t) / (E.card : ℝ) :=
    div_pos (Real.exp_pos _) hcard
  have hbalance : 0 ≤ (d / t) * sectionExponentialWeightSum E (fun i => μ i 0) j -
      (∑ i ∈ E, b i * Real.exp (-μ i 0 / j)) / j :=
    nonneg_of_mul_nonneg_right hD hfactor
  have hQ := sectionExponentialWeightSum_pos E (fun i => μ i 0) j hE
  apply (div_le_iff₀ (mul_pos hj hQ)).mpr
  have hsum : (∑ i ∈ E, b i * Real.exp (-μ i 0 / j)) / j ≤
      (d / t) * sectionExponentialWeightSum E (fun i => μ i 0) j :=
    sub_nonneg.mp hbalance
  have h := (div_le_iff₀ hj).mp hsum
  nlinarith

theorem quadraticDiscrepancy_hasDerivWithinAt (A d c : ℝ) :
    HasDerivWithinAt (fun ε : ℝ => A + d * ε + c * ε ^ 2) d (Set.Ioi 0) 0 := by
  simpa using (((hasDerivAt_const (0 : ℝ) A).fun_add
    ((hasDerivAt_id (0 : ℝ)).const_mul d)).fun_add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul c)).hasDerivWithinAt

theorem powerSeries_tangential_moment_upper_bound
    {σ K ι : Type*} [Fintype σ] [Field K]
    (E : Finset ι) (hE : E.Nonempty) (m : MonomialOrder σ)
    (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    (φ : ι → MvPowerSeries σ K) (p : ι → σ →₀ ℕ)
    (hp : ∀ i ∈ E, IsInitialMonomial (weightedMonomialOrder m w v hw) (φ i) (p i))
    (A d c t j : ℝ) (hj : 0 < j)
    (hmin : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      sectionExponentialObjective E t j (fun η => A + d * η + c * η ^ 2)
        (fun i => powerSeriesPerturbedValue m w v u hw (φ i)) 0 ≤
      sectionExponentialObjective E t j (fun η => A + d * η + c * η ^ 2)
        (fun i => powerSeriesPerturbedValue m w v u hw (φ i)) ε) :
    sectionExponentialMoment E (fun i => realExponentWeight w (p i))
      (fun i => (natExponentDegree v (p i) : ℝ)) j ≤ d / t := by
  have h := exponential_moment_upper_bound_of_minimum E hE t j hj _ _ d _
    (quadraticDiscrepancy_hasDerivWithinAt A d c)
    (fun i hi => powerSeriesPerturbedValue_hasDerivWithinAt m w v u hw (hp i hi)) hmin
  have hnum : (∑ i ∈ E, (natExponentDegree v (p i) : ℝ) *
      Real.exp (-realExponentWeight w (p i) / j)) =
      ∑ i ∈ E, (natExponentDegree v (p i) : ℝ) *
        Real.exp (-powerSeriesPerturbedValue m w v u hw (φ i) 0 / j) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [powerSeriesPerturbedValue_zero m w v u hw (hp i hi)]
  have hden : sectionExponentialWeightSum E (fun i => realExponentWeight w (p i)) j =
      sectionExponentialWeightSum E (fun i => powerSeriesPerturbedValue m w v u hw (φ i) 0) j := by
    unfold sectionExponentialWeightSum
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [powerSeriesPerturbedValue_zero m w v u hw (hp i hi)]
  unfold sectionExponentialMoment
  rw [hnum, hden]
  exact h

end MixedFujita
