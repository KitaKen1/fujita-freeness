/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MixedFormsRestrictedBound

/-!
Comparison of exponents in the root bound (13) (used for (20) of section 5.3 when the number of
tangent coordinates is smaller than the dimension of the image of the centre).

The uniform lower bound for the restricted dimensions I is stated with the dimension D' of the
subvariety as exponent: (s (q + 1 - s^D'))^D' ≤ D'! I. For an exponent D ≤ D' the same bound with
D in place of D' follows as soon as q ≥ 2 s^D' + 2^D' D'!, a threshold which depends only on s and
D': a larger exponent gives a faster growth.
-/

@[expose] public section

namespace MixedFujita

/-- The root bound in power form for a smaller exponent, above a threshold depending only on s
and the larger exponent. -/
theorem root_bound_pow_of_larger_exponent {D D' s q I : ℕ} (hDD' : D ≤ D') (hs : 1 ≤ s)
    (hq : 2 * s ^ D' + 2 ^ D' * D'.factorial ≤ q)
    (hI : (s * (q + 1 - s ^ D')) ^ D' ≤ D'.factorial * I) :
    (s * (q + 1 - s ^ D)) ^ D ≤ D.factorial * I := by
  rcases Nat.eq_or_lt_of_le hDD' with rfl | hlt
  · exact hI
  obtain ⟨k, rfl⟩ : ∃ k, D' = D + (k + 1) := ⟨D' - D - 1, by omega⟩
  have hfpos : 0 < (D + (k + 1)).factorial := Nat.factorial_pos _
  have hpow : s ^ D ≤ s ^ (D + (k + 1)) := Nat.pow_le_pow_right hs (by omega)
  obtain ⟨x, hx⟩ : ∃ x, x = s * (q + 1 - s ^ (D + (k + 1))) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = s * (q + 1 - s ^ D) := ⟨_, rfl⟩
  rw [← hx] at hI
  rw [← hy]
  have hx1 : 2 ^ (D + (k + 1)) * (D + (k + 1)).factorial ≤ x := by
    rw [hx]
    calc 2 ^ (D + (k + 1)) * (D + (k + 1)).factorial ≤ q + 1 - s ^ (D + (k + 1)) := by omega
      _ = 1 * (q + 1 - s ^ (D + (k + 1))) := (one_mul _).symm
      _ ≤ s * (q + 1 - s ^ (D + (k + 1))) := Nat.mul_le_mul_right _ hs
  have hy2 : y ≤ 2 * x := by
    rw [hy, hx]
    calc s * (q + 1 - s ^ D) ≤ s * (q + 1) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ ≤ s * (2 * (q + 1 - s ^ (D + (k + 1)))) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (s * (q + 1 - s ^ (D + (k + 1)))) := by ring
  have hxpos : 1 ≤ x :=
    le_trans (Nat.mul_pos (Nat.pow_pos (by norm_num)) hfpos) hx1
  have hkey : y ^ D * (D + (k + 1)).factorial ≤ x ^ (D + (k + 1)) := by
    calc y ^ D * (D + (k + 1)).factorial
        ≤ (2 * x) ^ D * (D + (k + 1)).factorial :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hy2 D)
      _ = x ^ D * (2 ^ D * (D + (k + 1)).factorial) := by rw [mul_pow]; ring
      _ ≤ x ^ D * (2 ^ (D + (k + 1)) * (D + (k + 1)).factorial) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _
            (Nat.pow_le_pow_right (by norm_num) (by omega)))
      _ ≤ x ^ D * x := Nat.mul_le_mul_left _ hx1
      _ ≤ x ^ D * x ^ (k + 1) := Nat.mul_le_mul_left _ (by
          calc x = x ^ 1 := (pow_one x).symm
            _ ≤ x ^ (k + 1) := Nat.pow_le_pow_right hxpos (by omega))
      _ = x ^ (D + (k + 1)) := (pow_add x D (k + 1)).symm
  have h1 : (D + (k + 1)).factorial * y ^ D ≤ (D + (k + 1)).factorial * (D.factorial * I) := by
    calc (D + (k + 1)).factorial * y ^ D = y ^ D * (D + (k + 1)).factorial := mul_comm _ _
      _ ≤ x ^ (D + (k + 1)) := hkey
      _ ≤ (D + (k + 1)).factorial * I := hI
      _ ≤ (D + (k + 1)).factorial * (D.factorial * I) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.factorial_pos D))
  exact Nat.le_of_mul_le_mul_left h1 hfpos

/-- The root bound for the exponent d + 1 from the bound in power form for a larger exponent. -/
theorem root_bound_of_larger_exponent {d D' s q I : ℕ} (hDD' : d + 1 ≤ D') (hs : 1 ≤ s)
    (hq : 2 * s ^ D' + 2 ^ D' * D'.factorial ≤ q)
    (hI : (s * (q + 1 - s ^ D')) ^ D' ≤ D'.factorial * I) :
    (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * I : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹ := by
  have h := root_bound_pow_of_larger_exponent hDD' hs hq hI
  have hle : s ^ (d + 1) ≤ q + 1 := by
    have h1 : s ^ (d + 1) ≤ s ^ D' := Nat.pow_le_pow_right hs hDD'
    omega
  have hcast : ((s * (q + 1 - s ^ (d + 1)) : ℕ) : ℝ) =
      (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) := by
    rw [Nat.cast_mul, Nat.cast_sub hle]
    push_cast
    ring
  rw [← hcast]
  refine le_rpow_inv_of_pow_le (Nat.cast_nonneg _) ?_
  exact_mod_cast h

end MixedFujita
