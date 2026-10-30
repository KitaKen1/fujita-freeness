/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InteriorStartBound

/-!
The opening dichotomy of Lemma 5 (§8). If the initial exponent sets grow like c j^n with
n! c ≥ (n+1)^n (that is A^n ≥ (n+1)^n), the lattice comparison gives averages of |γ|/j eventually
above every σ < (n/(n+1)) (n! c)^(1/n), and (n/(n+1)) (n! c)^(1/n) ≥ n. Either the averages are
eventually above some σ > n, the strict inequality (33), or n! c = (n+1)^n and for every ε > 0
the averages are frequently at most n + ε: the equality case, where some subsequence of the means
tends to n.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

/-- The opening dichotomy of Lemma 5. -/
theorem equality_case_dichotomy (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ)) {c : ℝ}
    (hc : 0 < c) (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    (hvol : ((n + 1 : ℕ) : ℝ) ^ n ≤ (n.factorial : ℝ) * c) :
    (∃ σ > (n : ℝ), ∀ᶠ j : ℕ in atTop,
        σ ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card) ∨
      ((n.factorial : ℝ) * c = ((n + 1 : ℕ) : ℝ) ^ n ∧ ∀ ε > 0, ∃ᶠ j : ℕ in atTop,
        (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card ≤ n + ε) := by
  set L : ℝ := (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ with hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) * c := mul_pos (by exact_mod_cast n.factorial_pos) hc
  -- L ≥ n, from (n! c)^(1/n) ≥ n + 1
  have hroot : ((n + 1 : ℕ) : ℝ) ≤ ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ := by
    have h := Real.rpow_le_rpow (by positivity) hvol (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (by positivity) hn.ne'] at h
  have hLn : (n : ℝ) ≤ L := by
    rw [hL]
    have h1 : (n : ℝ) = (n : ℝ) / (n + 1) * ((n + 1 : ℕ) : ℝ) := by
      push_cast
      field_simp
    calc (n : ℝ) = (n : ℝ) / (n + 1) * ((n + 1 : ℕ) : ℝ) := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left hroot (by positivity)
  set avg : ℕ → ℝ := fun j => (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card with havg
  by_cases hstrict : ∃ σ > (n : ℝ), ∀ᶠ j : ℕ in atTop, σ ≤ avg j
  · exact Or.inl hstrict
  right
  -- L ≤ n: otherwise the lattice bound gives the strict inequality
  have hLle : L ≤ n := by
    by_contra hgt
    push Not at hgt
    have hσ : ((n : ℝ) + L) / 2 < L := by linarith
    have hev := (eventually_average_degree_ge n hn E hc hN hσ).mono fun j h => h.2
    exact hstrict ⟨((n : ℝ) + L) / 2, by linarith, hev⟩
  have hLeq : L = n := le_antisymm hLle hLn
  refine ⟨?_, fun ε hε => ?_⟩
  · -- (n! c)^(1/n) = n + 1
    have hq : (n : ℝ) / (n + 1) ≠ 0 := by positivity
    have h2 : ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ * ((n : ℝ) / (n + 1)) = n := by
      rw [mul_comm]
      exact hLeq
    have h1 : ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ = ((n + 1 : ℕ) : ℝ) := by
      rw [eq_div_of_mul_eq hq h2]
      push_cast
      field_simp
    have h4 := congrArg (fun y : ℝ => y ^ n) h1
    rwa [Real.rpow_inv_natCast_pow hfac.le hn.ne'] at h4
  · -- the means are frequently at most n + ε
    by_contra hfr
    rw [Filter.not_frequently] at hfr
    exact hstrict ⟨(n : ℝ) + ε, by linarith, hfr.mono fun j hj => (not_le.mp hj).le⟩

end MixedFujita
