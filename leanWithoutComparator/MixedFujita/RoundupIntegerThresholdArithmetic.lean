/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryRoundup

/-! Exact integer pole inequalities for a negative boundary round-up. The
strict klt endpoint corresponds to a non-strict bound on the integer pole
order, including negative discriminant coefficients. -/

@[expose] public section

namespace MixedFujita

/-- Subtracting an integer from ceil(-b/d) is nonnegative exactly when the
corresponding denominator-cleared boundary coefficient is strictly below d. -/
theorem boundary_roundup_sub_integer_nonneg_iff (b k : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    0 ≤ ⌈-((b : ℝ) / (d : ℝ))⌉ - k ↔ b + (d : ℤ) * k < (d : ℤ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [show (0 ≤ ⌈-((b : ℝ) / (d : ℝ))⌉ - k) ↔
    k - 1 < ⌈-((b : ℝ) / (d : ℝ))⌉ by omega, Int.lt_ceil]
  rw [show -((b : ℝ) / (d : ℝ)) = -(b : ℝ) / (d : ℝ) by ring]
  rw [lt_div_iff₀ hdR]
  push_cast
  constructor
  · intro h
    have hR : (b : ℝ) + (d : ℝ) * (k : ℝ) < (d : ℝ) := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : (b : ℝ) + (d : ℝ) * (k : ℝ) < (d : ℝ) := by exact_mod_cast h
    nlinarith

/-- A strict rational klt threshold gives the exact integral discriminant
round-up pole bound; equality with an integral endpoint is excluded. -/
theorem integer_lt_threshold_iff_le_discriminant_roundup (p : ℤ) (t : ℚ) :
    (p : ℚ) < t ↔ p ≤ ⌈-(1 - t)⌉ := by
  rw [show -(1 - t) = t - 1 by ring, Int.ceil_sub_one]
  rw [show p ≤ ⌈t⌉ - 1 ↔ p < ⌈t⌉ by omega, Int.lt_ceil]

end MixedFujita
