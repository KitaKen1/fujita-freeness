/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.JetHilbertBound

/-!
The increment form of the jet comparison. Only an upper bound for the growth of
section dimensions is used: h(k+j) - h(k) ≤ C j (k+j+1)^(d-1). No asymptotic
leading coefficient or Hilbert polynomial is needed. With m^d ≤ b dim for the jet
spaces, every nonzero section of degree j ≥ 1 has order at most ⌈c⌉ j with the
explicit constant c = max 1 (b 2^(d-1) C), independent of the point.
-/

@[expose] public section

namespace MixedFujita

open Finset

/-- The explicit constant of the increment form of the jet comparison. -/
noncomputable def jetIncrementConstant (n : ℕ) (C b : ℝ) : ℝ :=
  max 1 (b * 2 ^ (n - 1) * C)

/-- Numerical core of the increment form. The constant is supplied and verified. -/
theorem jetIncrement_le_mul {n : ℕ} (hn : 1 ≤ n) {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (H : ℕ → ℝ) (hΔ : ∀ k j : ℕ, H (k + j) - H k ≤ C * j * ((k : ℝ) + j + 1) ^ (n - 1))
    {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) {J : ℝ} (hJ : (m : ℝ) ^ n ≤ b * J)
    (hgap : J + H (m - 1) ≤ H (j + (m - 1))) :
    (m : ℝ) ≤ jetIncrementConstant n C b * j := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  rcases le_or_gt m j with hmj | hjm
  · have hmj' : (m : ℝ) ≤ j := by exact_mod_cast hmj
    calc (m : ℝ) ≤ 1 * j := by linarith
      _ ≤ jetIncrementConstant n C b * j :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hj0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hstep := hΔ (m - 1) j
  rw [Nat.add_comm (m - 1) j] at hstep
  have hcast : ((m - 1 : ℕ) : ℝ) + j + 1 ≤ 2 * m := by
    have : (m - 1) + j + 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hpow : (((m - 1 : ℕ) : ℝ) + j + 1) ^ (n - 1) ≤ (2 * m) ^ (n - 1) :=
    pow_le_pow_left₀ (by positivity) hcast _
  have hJle : J ≤ C * j * (2 * m) ^ (n - 1) := by
    have h1 : J ≤ C * j * (((m - 1 : ℕ) : ℝ) + j + 1) ^ (n - 1) := by linarith
    exact h1.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hmn : (m : ℝ) ^ n ≤ b * (C * j * (2 * m) ^ (n - 1)) :=
    hJ.trans (mul_le_mul_of_nonneg_left hJle hb)
  have hpow' : (m : ℝ) ^ n = m * (m : ℝ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2pow : ((2 : ℝ) * m) ^ (n - 1) = 2 ^ (n - 1) * (m : ℝ) ^ (n - 1) := mul_pow _ _ _
  rw [hpow', h2pow] at hmn
  have hmpow : (0 : ℝ) < (m : ℝ) ^ (n - 1) := pow_pos hmpos _
  have hm' : (m : ℝ) ≤ b * 2 ^ (n - 1) * C * j := by
    have hmn' : (m : ℝ) * (m : ℝ) ^ (n - 1) ≤ (b * 2 ^ (n - 1) * C * j) * (m : ℝ) ^ (n - 1) := by
      calc (m : ℝ) * (m : ℝ) ^ (n - 1) ≤ b * (C * j * (2 ^ (n - 1) * (m : ℝ) ^ (n - 1))) := hmn
        _ = (b * 2 ^ (n - 1) * C * j) * (m : ℝ) ^ (n - 1) := by ring
    exact le_of_mul_le_mul_right hmn' hmpow
  calc (m : ℝ) ≤ b * 2 ^ (n - 1) * C * j := hm'
    _ ≤ jetIncrementConstant n C b * j :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hj0

/-- From order bounds at every positive level to a bound in ℕ∞. -/
theorem order_le_ceil_mul_of_levels {ord : ℕ∞} {c : ℝ} {j : ℕ}
    (hkey : ∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ ord → (m : ℝ) ≤ c * j) :
    ord ≤ ((⌈c⌉₊ * j : ℕ) : ℕ∞) := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  set N := ⌈c⌉₊ * j with hN
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ ord := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Order.add_one_le_of_lt hlt
  have hbound := hkey (N + 1) (by omega) hle
  have hceil : c * j ≤ (N : ℝ) := by
    rw [hN, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg j)
  have : ((N + 1 : ℕ) : ℝ) ≤ N := hbound.trans hceil
  push_cast at this
  linarith

/-- Increment form of the abstract graded order bound. Only the growth upper bound
h(k+j) - h(k) ≤ C j (k+j+1)^(d-1) of the section dimensions is required. -/
theorem gradedSection_order_le_of_jets_increment
    {K : Type*} [Field K]
    (V : ℕ → Type*) [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
    [∀ j, FiniteDimensional K (V j)]
    (mul : ∀ j k, V j → V k →ₗ[K] V (j + k))
    (hmul : ∀ j k (s : V j), s ≠ 0 → Function.Injective (mul j k s))
    (Q : ℕ → Type*) [∀ m, AddCommGroup (Q m)] [∀ m, Module K (Q m)]
    (ev : ∀ D m, V D →ₗ[K] Q m)
    (hsurj : ∀ D m, 1 ≤ m → m ≤ D + 1 → Function.Surjective (ev D m))
    (ord : ∀ j, V j → ℕ∞)
    (hvan : ∀ (j k m : ℕ) (s : V j) (t : V k), 1 ≤ m → (m : ℕ∞) ≤ ord j s →
      ev (j + k) m (mul j k s t) = 0)
    {n : ℕ} (hn : 1 ≤ n) {b : ℝ} (hb : 0 ≤ b)
    (hQ : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ^ n ≤ b * Module.finrank K (Q m))
    {C : ℝ} (hC : 0 ≤ C)
    (hΔ : ∀ k j : ℕ, (Module.finrank K (V (k + j)) : ℝ) - Module.finrank K (V k) ≤
      C * j * ((k : ℝ) + j + 1) ^ (n - 1))
    {j : ℕ} (hj : 1 ≤ j) (s : V j) (hs : s ≠ 0) :
    ord j s ≤ ((⌈jetIncrementConstant n C b⌉₊ * j : ℕ) : ℕ∞) := by
  apply order_le_ceil_mul_of_levels
  intro m hm hord
  have hle : LinearMap.range (mul j (m - 1) s) ≤ LinearMap.ker (ev (j + (m - 1)) m) := by
    rintro _ ⟨t, rfl⟩
    exact hvan j (m - 1) m s t hm hord
  have hsurj' := hsurj (j + (m - 1)) m hm (by omega)
  have hdim := finrank_add_finrank_le_of_range_le_ker _ hsurj' (mul j (m - 1) s)
    (hmul j (m - 1) s hs) hle
  have hgap : (Module.finrank K (Q m) : ℝ) + (Module.finrank K (V (m - 1)) : ℝ) ≤
      (Module.finrank K (V (j + (m - 1))) : ℝ) := by
    exact_mod_cast hdim
  exact jetIncrement_le_mul hn hC hb (fun k => (Module.finrank K (V k) : ℝ)) hΔ hj hm
    (hQ m hm) hgap

end MixedFujita
