/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MinimizationIntervalArithmetic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
The first step of §3.2: a minimizing sequence has a convergent subsequence. Along a minimizing
sequence of valuations and bases the discrepancies a_k = A(v_k) lie in [a_*, a^*] by (10) and
the normalized values q_{k,i} = v_k(s_{k,i})/A(v_k) lie in [0, C j] by Lemma 1, a compact set; a
subsequence converges to (a, q), the functional is continuous in (a, q), so its limit value is
the infimum, and some q_i is positive: otherwise the limit value would be e^(a/t) > 1. The
realization of the limit profile (flag closedness, retraction to a fixed model) is separate.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology Set

theorem continuous_minimizationFunctional_profile {N : ℕ} (j : ℕ) (t : ℝ) :
    Continuous fun p : ℝ × (Fin N → ℝ) =>
      minimizationFunctional j t p.1 (fun i => p.1 * p.2 i) := by
  unfold minimizationFunctional
  fun_prop

theorem minimizationFunctional_zero_profile {N : ℕ} (hN : 0 < N) (j : ℕ) (t a : ℝ) :
    minimizationFunctional j t a (fun _ : Fin N => a * 0) = Real.exp (a / t) := by
  unfold minimizationFunctional
  simp only [mul_zero, zero_div, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- §3.2: a minimizing sequence in [a_*, a^*] × [0, B]^N has a subsequence converging to a pair
whose value is the limit, with some positive normalized value when the limit is below 1. -/
theorem minimizing_sequence_limit {N : ℕ} (hN : 0 < N) (j : ℕ) {t aLow aHigh B f : ℝ}
    (ht : 0 < t) (haLow : 0 < aLow) (a : ℕ → ℝ) (q : ℕ → Fin N → ℝ)
    (ha : ∀ k, a k ∈ Icc aLow aHigh) (hq : ∀ k i, q k i ∈ Icc 0 B)
    (hF : Tendsto (fun k => minimizationFunctional j t (a k) (fun i => a k * q k i)) atTop (𝓝 f))
    (hf : f < 1) :
    ∃ a₀ ∈ Icc aLow aHigh, ∃ q₀ : Fin N → ℝ, (∀ i, q₀ i ∈ Icc 0 B) ∧
      minimizationFunctional j t a₀ (fun i => a₀ * q₀ i) = f ∧ (∃ i, 0 < q₀ i) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => a (φ k)) atTop (𝓝 a₀) ∧
        Tendsto (fun k => q (φ k)) atTop (𝓝 q₀) := by
  set S : Set (ℝ × (Fin N → ℝ)) := Icc aLow aHigh ×ˢ Set.pi univ (fun _ => Icc 0 B) with hS
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hmem : ∀ k, (a k, q k) ∈ S := fun k => ⟨ha k, fun i _ => hq k i⟩
  obtain ⟨p₀, hp₀, φ, hφ, hlim⟩ := hSc.tendsto_subseq hmem
  have hG := ((continuous_minimizationFunctional_profile (N := N) j t).tendsto p₀).comp hlim
  have hF' := hF.comp hφ.tendsto_atTop
  have hval : minimizationFunctional j t p₀.1 (fun i => p₀.1 * p₀.2 i) = f :=
    tendsto_nhds_unique hG hF'
  refine ⟨p₀.1, hp₀.1, p₀.2, fun i => hp₀.2 i (mem_univ i), hval, ?_, φ, hφ,
    (continuous_fst.tendsto p₀).comp hlim, (continuous_snd.tendsto p₀).comp hlim⟩
  by_contra hpos
  push Not at hpos
  have hzero : p₀.2 = fun _ => 0 := by
    funext i
    exact le_antisymm (hpos i) (hp₀.2 i (mem_univ i)).1
  have h1 : minimizationFunctional j t p₀.1 (fun i => p₀.1 * p₀.2 i) = Real.exp (p₀.1 / t) := by
    rw [hzero]
    exact minimizationFunctional_zero_profile hN j t p₀.1
  have h2 : 1 < Real.exp (p₀.1 / t) :=
    Real.one_lt_exp_iff.mpr (div_pos (haLow.trans_le hp₀.1.1) ht)
  rw [hval] at h1
  linarith

end MixedFujita
