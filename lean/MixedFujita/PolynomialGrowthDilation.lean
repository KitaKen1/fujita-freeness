/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IitakaGrowth

/-!
Polynomial growth exponents are unchanged by positive integral dilation when a fixed shift of
the dilated sequence dominates the original sequence. This avoids separate estimates on residue
classes. For eventual Cartier freeness the domination is multiplication by a nonzero section
of (q(j+M)-j)D, which is free as soon as M is large enough.
-/

@[expose] public section

open Filter

namespace MixedFujita

/-- Positive dilation preserves the full growth condition (frequent lower bound and everywhere
upper bound), given domination by one fixed shifted dilated sequence. -/
theorem polynomialGrowth_positive_dilation_iff {f : ℕ → ℝ} (hf0 : 0 ≤ f 0)
    {q M k : ℕ} (hq : 0 < q) (hshift : ∀ j : ℕ, f j ≤ f (q * (j + M))) :
    ((∃ c : ℝ, 0 < c ∧ ∃ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤ f j) ∧
      ∃ C : ℝ, ∀ j : ℕ, f j ≤ C * ((j : ℝ) + 1) ^ k) ↔
    ((∃ c : ℝ, 0 < c ∧ ∃ᶠ j : ℕ in atTop, c * (j : ℝ) ^ k ≤ f (q * j)) ∧
      ∃ C : ℝ, ∀ j : ℕ, f (q * j) ≤ C * ((j : ℝ) + 1) ^ k) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  constructor
  · rintro ⟨⟨c, hc, hlow⟩, C, hupp⟩
    have hC : 0 ≤ C := by simpa using hf0.trans (hupp 0)
    refine ⟨⟨c / ((M : ℝ) + 1) ^ k, by positivity, ?_⟩,
      C * (q : ℝ) ^ k, fun j => ?_⟩
    · rw [frequently_atTop]
      intro N
      obtain ⟨j, hj, hjlow⟩ := frequently_atTop.mp hlow (max N 1)
      have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (le_max_right N 1).trans hj
      have hbound : ((j + M : ℕ) : ℝ) ≤ ((M : ℝ) + 1) * j := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hj1 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      refine ⟨j + M, by omega, ?_⟩
      calc
        c / ((M : ℝ) + 1) ^ k * ((j + M : ℕ) : ℝ) ^ k
            ≤ c / ((M : ℝ) + 1) ^ k * (((M : ℝ) + 1) * j) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbound k) (by positivity)
        _ = c * (j : ℝ) ^ k := by rw [mul_pow]; field_simp
        _ ≤ f j := hjlow
        _ ≤ f (q * (j + M)) := hshift j
    · calc
        f (q * j) ≤ C * (((q * j : ℕ) : ℝ) + 1) ^ k := hupp _
        _ ≤ C * ((q : ℝ) * ((j : ℝ) + 1)) ^ k := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          nlinarith
        _ = C * (q : ℝ) ^ k * ((j : ℝ) + 1) ^ k := by rw [mul_pow]; ring
  · rintro ⟨⟨c, hc, hlow⟩, C, hupp⟩
    have hC : 0 ≤ C := by simpa using hf0.trans (by simpa using hupp 0)
    refine ⟨⟨c / (q : ℝ) ^ k, by positivity, ?_⟩,
      C * ((M : ℝ) + 1) ^ k, fun j => ?_⟩
    · rw [frequently_atTop]
      intro N
      obtain ⟨j, hj, hjlow⟩ := frequently_atTop.mp hlow N
      refine ⟨q * j, hj.trans (Nat.le_mul_of_pos_left j hq), ?_⟩
      calc
        c / (q : ℝ) ^ k * ((q * j : ℕ) : ℝ) ^ k = c * (j : ℝ) ^ k := by
          push_cast
          rw [mul_pow]
          field_simp
        _ ≤ f (q * j) := hjlow
    · calc
        f j ≤ f (q * (j + M)) := hshift j
        _ ≤ C * (((j + M : ℕ) : ℝ) + 1) ^ k := hupp _
        _ ≤ C * (((M : ℝ) + 1) * ((j : ℝ) + 1)) ^ k := by
          apply mul_le_mul_of_nonneg_left _ hC
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          nlinarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
            (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        _ = C * ((M : ℝ) + 1) ^ k * ((j : ℝ) + 1) ^ k := by rw [mul_pow]; ring

end MixedFujita
