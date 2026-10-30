/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Finsupp.Weight

/-!
A Bertini-free route to a uniform linear vanishing-order bound.
Suppose degree-D sections realize every jet below order m when m ≤ D + 1.
A nonzero degree-j section vanishing to order m then multiplies the
degree-(m-1) sections injectively into the kernel of a surjective jet map.
Comparing dimensions with two-sided Hilbert bounds gives order ≤ c j with the
explicit constant c = max 1 (b 2^(n-1) (a n + 2 C)), where m^n ≤ b · dim is the
jet-dimension bound: b = n! for simplex jets, b = n^n for coefficient boxes.
The geometric Hilbert bounds, jet surjectivity and jet dimensions are inputs.
-/

@[expose] public section

namespace MixedFujita

open Finset

/-- Rank-nullity in the form used for jet comparisons. -/
theorem finrank_add_finrank_le_of_range_le_ker {K V W Q : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Q] [Module K Q]
    (ev : V →ₗ[K] Q) (hev : Function.Surjective ev)
    (μ : W →ₗ[K] V) (hμ : Function.Injective μ)
    (hle : LinearMap.range μ ≤ LinearMap.ker ev) :
    Module.finrank K Q + Module.finrank K W ≤ Module.finrank K V := by
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hev, finrank_top] at hrn
  have hW : Module.finrank K W = Module.finrank K (LinearMap.range μ) :=
    (LinearMap.finrank_range_of_inj hμ).symm
  have hmono := Submodule.finrank_mono hle
  omega

/-- The binomial count of jets below order p + 1 in n variables. -/
theorem pow_le_factorial_mul_choose (p n : ℕ) :
    (p + 1) ^ n ≤ n.factorial * (p + n).choose n := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (p + 1) n

theorem pow_sub_pow_le_mul_pow {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (n : ℕ) :
    q ^ n - p ^ n ≤ n * (q - p) * q ^ (n - 1) := by
  rw [← geom_sum₂_mul]
  have hterm : ∀ i ∈ range n, q ^ i * p ^ (n - 1 - i) ≤ q ^ (n - 1) := by
    intro i hi
    have hi' : i ≤ n - 1 := by
      rw [mem_range] at hi
      omega
    calc q ^ i * p ^ (n - 1 - i) ≤ q ^ i * q ^ (n - 1 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hpq _)
            (pow_nonneg (hp.trans hpq) _)
      _ = q ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
  have hsum : ∑ i ∈ range n, q ^ i * p ^ (n - 1 - i) ≤ n * q ^ (n - 1) := by
    calc ∑ i ∈ range n, q ^ i * p ^ (n - 1 - i) ≤ ∑ _i ∈ range n, q ^ (n - 1) :=
          sum_le_sum hterm
      _ = n * q ^ (n - 1) := by simp
  calc (∑ i ∈ range n, q ^ i * p ^ (n - 1 - i)) * (q - p) ≤
        (n * q ^ (n - 1)) * (q - p) :=
        mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hpq)
    _ = n * (q - p) * q ^ (n - 1) := by ring

/-- The explicit jet-Hilbert constant. Here b is the factor in a jet-dimension lower
bound m^n ≤ b · dim; b = n! for simplex jets and b = n^n for coefficient boxes. -/
noncomputable def jetHilbertConstant (n : ℕ) (a C b : ℝ) : ℝ :=
  max 1 (b * 2 ^ (n - 1) * (a * n + 2 * C))

/-- The numerical heart of the jet comparison. If degree-(j+m-1) sections have at
least J more dimensions than degree-(m-1) sections, with m^n ≤ b J, two-sided
Hilbert bounds force m ≤ c j. The constant is supplied explicitly and verified. -/
theorem jetHilbert_le_mul {n : ℕ} (hn : 1 ≤ n) {a C b : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hb : 0 ≤ b)
    (H : ℕ → ℝ) (hH : ∀ k : ℕ, |H k - a * (k : ℝ) ^ n| ≤ C * ((k : ℝ) + 1) ^ (n - 1))
    {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) {J : ℝ} (hJ : (m : ℝ) ^ n ≤ b * J)
    (hgap : J + H (m - 1) ≤ H (j + (m - 1))) :
    (m : ℝ) ≤ jetHilbertConstant n a C b * j := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rcases le_or_gt m j with hmj | hjm
  · have hmj' : (m : ℝ) ≤ j := by exact_mod_cast hmj
    calc (m : ℝ) ≤ 1 * j := by linarith
      _ ≤ jetHilbertConstant n a C b * j :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hj0
  -- Now j < m. Put p = m - 1 and q = j + p.
  set p := m - 1 with hpdef
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hqp : ((j + p : ℕ) : ℝ) = j + p := by push_cast; ring
  have hHq := (abs_le.mp (hH (j + p))).2
  have hHp := (abs_le.mp (hH p)).1
  rw [hqp] at hHq
  have hdiff := pow_sub_pow_le_mul_pow hp0 (by linarith : (p : ℝ) ≤ j + p) n
  have hq2 : (j : ℝ) + p ≤ 2 * m := by
    have h1 : (j : ℝ) < m := by exact_mod_cast hjm
    have h2 : (p : ℝ) ≤ m := by exact_mod_cast (show p ≤ m by omega)
    linarith
  have hq12 : (j : ℝ) + p + 1 ≤ 2 * m := by
    have : j + p + 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hp12 : (p : ℝ) + 1 ≤ 2 * m := by
    have : p + 1 ≤ 2 * m := by omega
    exact_mod_cast this
  have hqpow : ((j : ℝ) + p) ^ (n - 1) ≤ (2 * m) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) hq2 _
  have hq1pow : ((j : ℝ) + p + 1) ^ (n - 1) ≤ (2 * m) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) hq12 _
  have hp1pow : ((p : ℝ) + 1) ^ (n - 1) ≤ (2 * m) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) hp12 _
  have hupper : J ≤ (2 * m) ^ (n - 1) * (a * n * j + 2 * C) := by
    have hgap' : J ≤ H (j + p) - H p := by linarith
    have hsub : (j : ℝ) + p - p = j := by ring
    rw [hsub] at hdiff
    have ha1 : a * (((j : ℝ) + p) ^ n - (p : ℝ) ^ n) ≤
        a * (n * j * (2 * m) ^ (n - 1)) := by
      apply mul_le_mul_of_nonneg_left _ ha
      calc ((j : ℝ) + p) ^ n - (p : ℝ) ^ n ≤ n * j * ((j : ℝ) + p) ^ (n - 1) := hdiff
        _ ≤ n * j * (2 * m) ^ (n - 1) := by
            apply mul_le_mul_of_nonneg_left hqpow
            positivity
    have hC1 : C * ((j : ℝ) + p + 1) ^ (n - 1) ≤ C * (2 * m) ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hq1pow hC
    have hC2 : C * ((p : ℝ) + 1) ^ (n - 1) ≤ C * (2 * m) ^ (n - 1) :=
      mul_le_mul_of_nonneg_left hp1pow hC
    nlinarith
  have hmn : (m : ℝ) ^ n ≤ b * ((2 * m) ^ (n - 1) * (a * n * j + 2 * C)) :=
    hJ.trans (mul_le_mul_of_nonneg_left hupper hb)
  have hpow : (m : ℝ) ^ n = m * (m : ℝ) ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2pow : ((2 : ℝ) * m) ^ (n - 1) = 2 ^ (n - 1) * (m : ℝ) ^ (n - 1) := mul_pow _ _ _
  rw [hpow, h2pow] at hmn
  have hmpow : (0 : ℝ) < (m : ℝ) ^ (n - 1) := pow_pos hmpos _
  have hm' : (m : ℝ) ≤ b * 2 ^ (n - 1) * (a * n * j + 2 * C) := by
    have hmn' : (m : ℝ) * (m : ℝ) ^ (n - 1) ≤
        (b * 2 ^ (n - 1) * (a * n * j + 2 * C)) * (m : ℝ) ^ (n - 1) := by
      calc (m : ℝ) * (m : ℝ) ^ (n - 1) ≤
            b * (2 ^ (n - 1) * (m : ℝ) ^ (n - 1) * (a * n * j + 2 * C)) := hmn
        _ = (b * 2 ^ (n - 1) * (a * n * j + 2 * C)) * (m : ℝ) ^ (n - 1) := by ring
    exact le_of_mul_le_mul_right hmn' hmpow
  have hlin : b * 2 ^ (n - 1) * (a * n * j + 2 * C) ≤
      b * 2 ^ (n - 1) * (a * n + 2 * C) * j := by
    have hcoef : (0 : ℝ) ≤ b * 2 ^ (n - 1) := by positivity
    have h2C : 2 * C ≤ 2 * C * j := by nlinarith
    calc b * 2 ^ (n - 1) * (a * n * j + 2 * C) ≤
          b * 2 ^ (n - 1) * (a * n * j + 2 * C * j) :=
          mul_le_mul_of_nonneg_left (by linarith) hcoef
      _ = b * 2 ^ (n - 1) * (a * n + 2 * C) * j := by ring
  calc (m : ℝ) ≤ b * 2 ^ (n - 1) * (a * n + 2 * C) * j := hm'.trans hlin
    _ ≤ jetHilbertConstant n a C b * j :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hj0

/-- The coefficient box of side (m-1)/n + 1 has at least m^n / n^n points. -/
theorem pow_le_pow_mul_boxSide (n m : ℕ) (hn : 1 ≤ n) :
    (m : ℝ) ^ n ≤ (n : ℝ) ^ n * (((m - 1) / n + 1 : ℕ) : ℝ) ^ n := by
  have hle : m ≤ n * ((m - 1) / n + 1) := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · omega
    · have h := Nat.lt_mul_div_succ (m - 1) (show 0 < n by omega)
      omega
  have hle' : (m : ℝ) ≤ (n : ℝ) * (((m - 1) / n + 1 : ℕ) : ℝ) := by exact_mod_cast hle
  rw [← mul_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg m) hle' n

/-- Every exponent in the coefficient box of side (m-1)/n + 1 has total degree < m. -/
theorem boxSide_degree_lt (n m : ℕ) (hm : 1 ≤ m) (p : Fin n →₀ ℕ)
    (hp : ∀ i, p i ≤ (m - 1) / n) : p.degree < m := by
  rw [Finsupp.degree_eq_sum]
  calc ∑ i, p i ≤ ∑ _i : Fin n, (m - 1) / n := Finset.sum_le_sum fun i _ => hp i
    _ = n * ((m - 1) / n) := by simp
    _ ≤ m - 1 := Nat.mul_div_le (m - 1) n
    _ < m := by omega

/-- Abstract graded form of the Bertini-free order bound. Sections of each degree form
finite-dimensional spaces with an injective multiplication by nonzero sections. A jet
map of each level m ≥ 1 is surjective in every degree D ≥ m - 1 and kills products with
a section of order at least m. The jet spaces satisfy m^n ≤ b · dim, and the section
dimensions satisfy two-sided Hilbert bounds. Then every nonzero section of degree
j ≥ 1 has order at most ⌈c⌉₊ j, with the explicit constant c of
`jetHilbertConstant`. The constant does not depend on the point. -/
theorem gradedSection_order_le_of_jets_hilbert
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
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hH : ∀ k : ℕ, |(Module.finrank K (V k) : ℝ) - a * (k : ℝ) ^ n| ≤
      C * ((k : ℝ) + 1) ^ (n - 1))
    {j : ℕ} (hj : 1 ≤ j) (s : V j) (hs : s ≠ 0) :
    ord j s ≤ ((⌈jetHilbertConstant n a C b⌉₊ * j : ℕ) : ℕ∞) := by
  have hkey : ∀ m : ℕ, 1 ≤ m → (m : ℕ∞) ≤ ord j s →
      (m : ℝ) ≤ jetHilbertConstant n a C b * j := by
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
    exact jetHilbert_le_mul hn ha hC hb (fun k => (Module.finrank K (V k) : ℝ)) hH hj hm
      (hQ m hm) hgap
  by_contra hlt
  replace hlt := not_le.mp hlt
  set N := ⌈jetHilbertConstant n a C b⌉₊ * j with hN
  have hle : ((N + 1 : ℕ) : ℕ∞) ≤ ord j s := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Order.add_one_le_of_lt hlt
  have hbound := hkey (N + 1) (by omega) hle
  have hceil : jetHilbertConstant n a C b * j ≤ (N : ℝ) := by
    rw [hN, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg j)
  have : ((N + 1 : ℕ) : ℝ) ≤ N := hbound.trans hceil
  push_cast at this
  linarith

end MixedFujita
