/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Order.Antichain
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Monomial valuations with real weights and the attainment of the minimum of §3.2 on a fixed model.
By Dickson's lemma the support of a nonzero power series has finitely many minimal exponents and
every exponent of the support lies above one of them, so for nonnegative real weights u the value
v_u(f) = min over the support of u · β is the least u-weight of a minimal exponent. It is the
minimum of finitely many linear functions of u, hence continuous in u, homogeneous of degree one,
and for natural weights it is the weighted order. On a fixed layer with discrepancy A(u) = Σ a_i u_i
(a_i > 0), the normalized weights form the compact simplex Σ a_i u_i = 1, u ≥ 0, and the scale lies
in the compact interval [a_*, a^*] of §3.1; the functional
(1/N) Σ_k exp(λ/t - λ v_u(F_k)/j) is continuous in (λ, u), so its infimum over the scales and
normalized weights is attained. Weights that vanish are allowed.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries Finset

variable {σ K : Type*} [Field K] [Fintype σ]

/-- The exponents with nonzero coefficient. -/
def powerSeriesSupport (f : MvPowerSeries σ K) : Set (σ →₀ ℕ) := {β | coeff β f ≠ 0}

theorem powerSeriesSupport_minimal_finite (f : MvPowerSeries σ K) :
    {β | Minimal (· ∈ powerSeriesSupport f) β}.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)

/-- The minimal exponents of the support: a finite set. -/
noncomputable def minimalExponents (f : MvPowerSeries σ K) : Finset (σ →₀ ℕ) :=
  (powerSeriesSupport_minimal_finite f).toFinset

theorem mem_minimalExponents {f : MvPowerSeries σ K} {μ : σ →₀ ℕ} :
    μ ∈ minimalExponents f ↔ Minimal (· ∈ powerSeriesSupport f) μ :=
  Set.Finite.mem_toFinset _

theorem exists_minimalExponent_le {f : MvPowerSeries σ K} {β : σ →₀ ℕ}
    (hβ : β ∈ powerSeriesSupport f) : ∃ μ ∈ minimalExponents f, μ ≤ β := by
  obtain ⟨μ, hμ, hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE _).exists_le_minimal hβ
  exact ⟨μ, mem_minimalExponents.mpr hmin, hμ⟩

theorem minimalExponents_nonempty {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    (minimalExponents f).Nonempty := by
  obtain ⟨β, hβ⟩ := MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f |>.mp hf
  obtain ⟨μ, hμ, -⟩ := exists_minimalExponent_le (f := f) (β := β) hβ
  exact ⟨μ, hμ⟩

open Classical in
/-- The monomial valuation with real weights u: the least u-weight of a minimal exponent. -/
noncomputable def realWeightedOrder (u : σ → ℝ) (f : MvPowerSeries σ K) : ℝ :=
  if h : f = 0 then 0 else
    (minimalExponents f).inf' (minimalExponents_nonempty h) (fun μ => ∑ i, u i * μ i)

theorem realWeightedOrder_le {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i) {f : MvPowerSeries σ K}
    (hf : f ≠ 0) {β : σ →₀ ℕ} (hβ : coeff β f ≠ 0) :
    realWeightedOrder u f ≤ ∑ i, u i * β i := by
  obtain ⟨μ, hμ, hle⟩ := exists_minimalExponent_le (f := f) (β := β) hβ
  rw [realWeightedOrder, dite_eq_right hf]
  refine (Finset.inf'_le _ hμ).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle i) (hu i)

theorem exists_coeff_realWeightedOrder (u : σ → ℝ) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    ∃ β, coeff β f ≠ 0 ∧ ∑ i, u i * β i = realWeightedOrder u f := by
  obtain ⟨μ, hμ, heq⟩ := Finset.exists_mem_eq_inf' (minimalExponents_nonempty hf)
    (fun μ => ∑ i, u i * μ i)
  refine ⟨μ, (mem_minimalExponents.mp hμ).1, ?_⟩
  rw [realWeightedOrder, dite_eq_right hf, heq]

/-- For natural weights the real-weighted order is the weighted order. -/
theorem realWeightedOrder_natCast (w : σ → ℕ) {f : MvPowerSeries σ K} (hf : f ≠ 0) :
    realWeightedOrder (fun i => (w i : ℝ)) f = ((f.weightedOrder w).toNat : ℝ) := by
  have hfin : ((f.weightedOrder w).toNat : ℕ∞) = f.weightedOrder w :=
    (ne_zero_iff_weightedOrder_finite w).mp hf
  apply le_antisymm
  · obtain ⟨β, hβ, hw⟩ := exists_coeff_ne_zero_and_weightedOrder w hfin
    have hwβ : Finsupp.weight w β = (f.weightedOrder w).toNat := by
      have h : (Finsupp.weight w β : ℕ∞) = (f.weightedOrder w).toNat := hw.trans hfin.symm
      exact_mod_cast h
    refine (realWeightedOrder_le (fun i => Nat.cast_nonneg (w i)) hf hβ).trans_eq ?_
    rw [← hwβ, Finsupp.weight_eq_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; push_cast; ring
  · obtain ⟨β, hβ, heq⟩ := exists_coeff_realWeightedOrder (fun i => (w i : ℝ)) hf
    rw [← heq]
    have h := weightedOrder_le w hβ
    rw [← hfin] at h
    have h' : (f.weightedOrder w).toNat ≤ Finsupp.weight w β := by exact_mod_cast h
    have h'' : ((f.weightedOrder w).toNat : ℝ) ≤ (Finsupp.weight w β : ℝ) := by exact_mod_cast h'
    refine h''.trans_eq ?_
    rw [Finsupp.weight_eq_sum]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]; push_cast; ring

/-- The real-weighted order is homogeneous of degree one in the weights. -/
theorem realWeightedOrder_smul {c : ℝ} (hc : 0 ≤ c) (u : σ → ℝ) (f : MvPowerSeries σ K) :
    realWeightedOrder (c • u) f = c * realWeightedOrder u f := by
  by_cases hf : f = 0
  · rw [realWeightedOrder, dite_eq_left hf, realWeightedOrder, dite_eq_left hf, mul_zero]
  rw [realWeightedOrder, dite_eq_right hf, realWeightedOrder, dite_eq_right hf]
  apply le_antisymm
  · obtain ⟨μ, hμ, heq⟩ := Finset.exists_mem_eq_inf' (minimalExponents_nonempty hf)
      (fun μ => ∑ i, u i * μ i)
    rw [heq]
    refine (Finset.inf'_le _ hμ).trans_eq ?_
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · obtain ⟨μ, hμ, heq⟩ := Finset.exists_mem_eq_inf' (minimalExponents_nonempty hf)
      (fun μ => ∑ i, (c • u) i * μ i)
    rw [heq]
    have h := Finset.inf'_le (fun μ => ∑ i, u i * μ i) hμ
    calc c * (minimalExponents f).inf' _ (fun μ => ∑ i, u i * μ i) ≤ c * ∑ i, u i * μ i :=
          mul_le_mul_of_nonneg_left h hc
      _ = ∑ i, (c • u) i * μ i := by
          simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring

/-- The real-weighted order is continuous in the weights. -/
theorem continuous_realWeightedOrder (f : MvPowerSeries σ K) :
    Continuous (fun u : σ → ℝ => realWeightedOrder u f) := by
  by_cases hf : f = 0
  · have h : (fun u : σ → ℝ => realWeightedOrder u f) = fun _ => 0 := by
      funext u
      rw [realWeightedOrder, dite_eq_left hf]
    rw [h]
    exact continuous_const
  have h : (fun u : σ → ℝ => realWeightedOrder u f) = fun u : σ → ℝ =>
      (minimalExponents f).inf' (minimalExponents_nonempty hf) (fun μ => ∑ i, u i * μ i) := by
    funext u
    rw [realWeightedOrder, dite_eq_right hf]
  rw [h]
  refine Continuous.finset_inf'_apply (minimalExponents_nonempty hf) fun μ _ => ?_
  fun_prop

/-- The normalized weights of a layer: u ≥ 0 with Σ a_i u_i = 1. -/
def normalizedWeights (a : σ → ℝ) : Set (σ → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, a i * u i = 1}

theorem isCompact_normalizedWeights {a : σ → ℝ} (ha : ∀ i, 0 < a i) :
    IsCompact (normalizedWeights a) := by
  have hbox : IsCompact (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (1 / a i)) :=
    isCompact_univ_pi fun i => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {u : σ → ℝ | ∀ i, 0 ≤ u i} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {u : σ → ℝ | ∑ i, a i * u i = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    exact h1.inter h2
  · rintro u ⟨hu0, hu1⟩
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    intro i
    refine ⟨hu0 i, ?_⟩
    rw [le_div_iff₀ (ha i), mul_comm]
    have h : a i * u i ≤ ∑ k, a k * u k :=
      Finset.single_le_sum (f := fun k => a k * u k) (fun k _ => mul_nonneg (ha k).le (hu0 k))
        (Finset.mem_univ i)
    linarith

theorem normalizedWeights_nonempty [Nonempty σ] {a : σ → ℝ} (ha : ∀ i, 0 < a i) :
    (normalizedWeights a).Nonempty := by
  refine ⟨fun i => 1 / ((Fintype.card σ : ℝ) * a i), fun i => ?_, ?_⟩
  · have := ha i
    positivity
  · have hcard : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
    have h : ∀ i, a i * (1 / ((Fintype.card σ : ℝ) * a i)) = 1 / (Fintype.card σ : ℝ) := by
      intro i
      have := (ha i).ne'
      field_simp
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp

/-- §3.2 on a fixed layer: the functional (1/N) Σ_k exp(λ/t - λ v_u(F_k)/j) attains its infimum
over the scales λ ∈ [a_*, a^*] and the normalized weights u. -/
theorem exists_minimizer_scale_weights [Nonempty σ] {ι : Type*} [Fintype ι]
    (F : ι → MvPowerSeries σ K) {a : σ → ℝ} (ha : ∀ i, 0 < a i) (j : ℕ) (t : ℝ)
    {aLow aHigh : ℝ} (hlh : aLow ≤ aHigh) :
    ∃ p₀ ∈ Set.Icc aLow aHigh ×ˢ normalizedWeights a, ∀ p ∈ Set.Icc aLow aHigh ×ˢ normalizedWeights a,
      (∑ k, Real.exp (p₀.1 / t - p₀.1 * realWeightedOrder p₀.2 (F k) / j)) / Fintype.card ι ≤
        (∑ k, Real.exp (p.1 / t - p.1 * realWeightedOrder p.2 (F k) / j)) / Fintype.card ι := by
  have hK : IsCompact (Set.Icc aLow aHigh ×ˢ normalizedWeights a) :=
    isCompact_Icc.prod (isCompact_normalizedWeights ha)
  have hne : (Set.Icc aLow aHigh ×ˢ normalizedWeights a).Nonempty :=
    (Set.nonempty_Icc.mpr hlh).prod (normalizedWeights_nonempty ha)
  have hcont : Continuous (fun p : ℝ × (σ → ℝ) =>
      (∑ k, Real.exp (p.1 / t - p.1 * realWeightedOrder p.2 (F k) / j)) / Fintype.card ι) := by
    have hv : ∀ k, Continuous (fun p : ℝ × (σ → ℝ) => realWeightedOrder p.2 (F k)) :=
      fun k => (continuous_realWeightedOrder (F k)).comp continuous_snd
    refine Continuous.div_const (continuous_finsetSum _ fun k _ => ?_) _
    exact Real.continuous_exp.comp ((continuous_fst.div_const _).sub
      ((continuous_fst.mul (hv k)).div_const _))
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  exact ⟨p₀, hp₀, fun p hp => hmin hp⟩

end MixedFujita
