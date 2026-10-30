/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Tactic

/-! 係数比降下の有限整数冪評価と明示反復回数。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
namespace MixedFujita
set_option maxHeartbeats 1600000

/-- A completely finite integer estimate controls the coefficient descent;
no rational approximation or limit argument is needed. -/
theorem integer_descent_power_bound (d s : ℕ) :
    (s + d) * d ^ s ≤ d * (d + 1) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hp : d ^ s ≤ (d + 1) ^ s := Nat.pow_le_pow_left (Nat.le_succ d) s
    calc
      (s + 1 + d) * d ^ (s + 1) = d * ((s + d) * d ^ s) + d * d ^ s := by ring
      _ ≤ d * (d * (d + 1) ^ s) + d * (d + 1) ^ s :=
        Nat.add_le_add (Nat.mul_le_mul_left d ih) (Nat.mul_le_mul_left d hp)
      _ = d * (d + 1) ^ (s + 1) := by ring


/-- After exactly d*k updates, the ample coefficient is at most the nef
coefficient in the explicit sequence ((d+1)^s, k*d^s). -/
theorem integer_descent_coefficients_eventually_ordered (d k : ℕ) (hd : 0 < d) :
    k * d ^ (d * k) ≤ (d + 1) ^ (d * k) := by
  have h := integer_descent_power_bound d (d * k)
  have he : (d * k + d) * d ^ (d * k) = d * ((k + 1) * d ^ (d * k)) := by ring
  rw [he] at h
  have h' := Nat.le_of_mul_le_mul_left h hd
  exact (Nat.mul_le_mul_right _ (Nat.le_succ k)).trans h'

end MixedFujita
