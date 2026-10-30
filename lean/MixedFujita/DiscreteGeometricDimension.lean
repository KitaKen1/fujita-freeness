/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Tactic.Lift

/-! 普通の有限幾何次元の離散的前段階二分。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita

/-- A finite ordinary dimension bound has the expected discrete predecessor
alternative, also including the empty-space bottom value. -/
theorem withBotENat_le_succ_cases (d : WithBot ℕ∞) (n : ℕ)
    (hd : d ≤ (n + 1 : ℕ)) : d ≤ n ∨ d = (n + 1 : ℕ) := by
  cases d with
  | bot => exact Or.inl bot_le
  | coe d =>
    have hd' : d ≤ (n + 1 : ℕ) := by exact_mod_cast hd
    have htop : d ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd'
    lift d to ℕ using htop with k
    have hk : k ≤ n + 1 := by exact_mod_cast hd'
    by_cases hkn : k ≤ n
    · left
      exact_mod_cast hkn
    · right
      have heq : k = n + 1 := le_antisymm hk (Nat.succ_le_of_lt (lt_of_not_ge hkn))
      exact congrArg (fun a : ℕ => (a : WithBot ℕ∞)) heq

end MixedFujita
