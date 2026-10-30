/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SimplexMoment
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Complex.Exponential

/-!
The starting point of §7 (and of §8 after (33)): the interior condition (7) at a smooth point.
N lattice points of ℕ^n have average total degree at least (n/(n+1)) (n! N)^(1/n) - n, so if the
numbers N_j of initial exponents grow like c j^n, the averages S_j of |γ|/j satisfy
liminf S_j ≥ (n/(n+1)) (n! c)^(1/n): the bound (32). If this exceeds n/b, choose t_0 < b with
n/t_0 below the liminf; the derivative of F_{j,t}(ζ ord) = (1/N_j) Σ exp(ζ n/t - ζ |γ|/j) at ζ = 0
is then at most n/t_0 - liminf S_j < 0 uniformly in j and t ∈ [t_0, b], and the quadratic
remainder is uniform because |γ|/j ≤ C (the uniform order bound). Hence one small ζ > 0 and one
δ > 0 give F_{j,t}(ζ ord) ≤ 1 - δ for all large j and all t ∈ [t_0, b].
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

/-- The lattice comparison behind (32): N points of ℕ^n have average total degree at least
(n/(n+1)) (n! N)^(1/n) - n. -/
theorem average_degree_lower_bound (n : ℕ) (hn : 0 < n) (E : Finset (Fin n → ℕ))
    (hE : E.Nonempty) :
    (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * E.card) ^ (n : ℝ)⁻¹ - n ≤
      (∑ γ ∈ E, ((∑ i, γ i : ℕ) : ℝ)) / E.card := by
  have h := simplex_moment_lower_bound n hn E
  set R := ((n.factorial : ℝ) * E.card) ^ (n : ℝ)⁻¹ with hR
  have hc : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hRn : R ^ n = (n.factorial : ℝ) * E.card := Real.rpow_inv_natCast_pow (by positivity) hn.ne'
  have hpow : R ^ (n + 1) = (n.factorial : ℝ) * E.card * R := by rw [pow_succ, hRn]
  rw [hpow] at h
  have hsum : ∑ γ ∈ E, (((∑ i, γ i) + n : ℕ) : ℝ) =
      (∑ γ ∈ E, ((∑ i, γ i : ℕ) : ℝ)) + n * E.card := by
    simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum] at h
  have hl : (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * E.card * R) / n.factorial =
      (n : ℝ) / (n + 1) * R * E.card := by
    field_simp
  rw [hl] at h
  rw [le_div_iff₀ hc]
  have hexp : ((n : ℝ) / (n + 1) * R - n) * E.card =
      (n : ℝ) / (n + 1) * R * E.card - n * E.card := by
    ring
  rw [hexp]
  linarith

/-- e^x ≤ 1 + x + K^2 for |x| ≤ K ≤ 1. -/
theorem exp_le_one_add_add_sq {x K : ℝ} (hK : K ≤ 1) (hx : |x| ≤ K) :
    Real.exp x ≤ 1 + x + K ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (hx.trans hK)
  have h2 : x ^ 2 ≤ K ^ 2 := by
    have h3 := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at h3
  linarith [le_abs_self (Real.exp x - 1 - x)]

/-- §7: a uniformly negative derivative at ζ = 0 and a uniform quadratic remainder give one ζ
and one δ for all large j and all t ∈ [t_0, b]. -/
theorem uniform_interior_start {ι : Type*} (E : ℕ → Finset ι) (a : ℕ → ι → ℝ) {A₀ b C σ : ℝ}
    (hA₀ : 0 < A₀) (hb : 0 < b) (hC : 0 ≤ C) (hσ : A₀ / b < σ)
    (hE : ∀ᶠ j in atTop, (E j).Nonempty)
    (ha : ∀ᶠ j in atTop, ∀ γ ∈ E j, 0 ≤ a j γ ∧ a j γ ≤ C)
    (hmean : ∀ᶠ j in atTop, σ ≤ (∑ γ ∈ E j, a j γ) / (E j).card) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j in atTop, ∀ t, t₀ ≤ t → t ≤ b →
      (∑ γ ∈ E j, Real.exp (ζ * A₀ / t - ζ * a j γ)) / (E j).card ≤ 1 - δ := by
  have hσpos : 0 < σ := (div_pos hA₀ hb).trans hσ
  have hlt : A₀ / σ < b := by
    rw [div_lt_iff₀ hσpos]
    rw [div_lt_iff₀ hb] at hσ
    linarith
  set t₀ := (A₀ / σ + b) / 2 with ht₀
  have hAσ : 0 < A₀ / σ := div_pos hA₀ hσpos
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀b : t₀ < b := by linarith
  have ht₀σ : A₀ / σ < t₀ := by linarith
  set κ := A₀ / t₀ with hκ
  have hκσ : κ < σ := by
    rw [hκ, div_lt_iff₀ ht₀pos]
    rw [div_lt_iff₀ hσpos] at ht₀σ
    linarith
  have hκ0 : 0 < κ := div_pos hA₀ ht₀pos
  set m := σ - κ with hm
  have hm0 : 0 < m := sub_pos.mpr hκσ
  set K := κ + C + 1 with hK
  have hK0 : 0 < K := by positivity
  set ζ := min (1 / K) (m / (2 * K ^ 2)) with hζ
  have hζ0 : 0 < ζ := lt_min (by positivity) (by positivity)
  refine ⟨t₀, ht₀pos, ht₀b, ζ, hζ0, ζ * m / 2, by positivity, ?_⟩
  filter_upwards [hE, ha, hmean] with j hEj haj hmj
  intro t ht₀t htb
  have htpos : 0 < t := ht₀pos.trans_le ht₀t
  have hAt : A₀ / t ≤ κ := div_le_div_of_nonneg_left hA₀.le ht₀pos ht₀t
  have hcard : (0 : ℝ) < (E j).card := by exact_mod_cast hEj.card_pos
  have hζK : ζ * K ≤ 1 := by
    have h1 := min_le_left (1 / K) (m / (2 * K ^ 2))
    calc ζ * K ≤ 1 / K * K := mul_le_mul_of_nonneg_right h1 hK0.le
      _ = 1 := by field_simp
  have hAt' : ζ * A₀ / t ≤ ζ * κ := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hAt hζ0.le
  have hterm : ∀ γ ∈ E j, Real.exp (ζ * A₀ / t - ζ * a j γ) ≤
      1 + (ζ * A₀ / t - ζ * a j γ) + (ζ * K) ^ 2 := by
    intro γ hγ
    obtain ⟨h0, hCγ⟩ := haj γ hγ
    apply exp_le_one_add_add_sq hζK
    rw [abs_le]
    have hle : ζ * a j γ ≤ ζ * K := mul_le_mul_of_nonneg_left (by linarith) hζ0.le
    have hge : 0 ≤ ζ * a j γ := mul_nonneg hζ0.le h0
    have hA0 : 0 ≤ ζ * A₀ / t := by positivity
    have hκK : ζ * κ ≤ ζ * K := mul_le_mul_of_nonneg_left (by linarith) hζ0.le
    constructor <;> linarith
  have hsum := Finset.sum_le_sum hterm
  have hsplit : ∑ γ ∈ E j, (1 + (ζ * A₀ / t - ζ * a j γ) + (ζ * K) ^ 2) =
      (E j).card + (E j).card * (ζ * A₀ / t) + (E j).card * (ζ * K) ^ 2 -
        ζ * ∑ γ ∈ E j, a j γ := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have hmj' : σ * (E j).card ≤ ∑ γ ∈ E j, a j γ := (le_div_iff₀ hcard).mp hmj
  have hsq : (ζ * K) ^ 2 ≤ ζ * m / 2 := by
    have h2 := min_le_right (1 / K) (m / (2 * K ^ 2))
    have h3 : ζ * K ^ 2 ≤ m / 2 := by
      calc ζ * K ^ 2 ≤ m / (2 * K ^ 2) * K ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = m / 2 := by field_simp
    have h4 : ζ * (ζ * K ^ 2) ≤ ζ * (m / 2) := mul_le_mul_of_nonneg_left h3 hζ0.le
    calc (ζ * K) ^ 2 = ζ * (ζ * K ^ 2) := by ring
      _ ≤ ζ * (m / 2) := h4
      _ = ζ * m / 2 := by ring
  have e1 : (E j).card * (ζ * A₀ / t) ≤ (E j).card * (ζ * κ) :=
    mul_le_mul_of_nonneg_left hAt' hcard.le
  have e2 : (E j).card * (ζ * K) ^ 2 ≤ (E j).card * (ζ * m / 2) :=
    mul_le_mul_of_nonneg_left hsq hcard.le
  have e3 : ζ * (σ * (E j).card) ≤ ζ * ∑ γ ∈ E j, a j γ := mul_le_mul_of_nonneg_left hmj' hζ0.le
  rw [div_le_iff₀ hcard]
  calc ∑ γ ∈ E j, Real.exp (ζ * A₀ / t - ζ * a j γ)
      ≤ ∑ γ ∈ E j, (1 + (ζ * A₀ / t - ζ * a j γ) + (ζ * K) ^ 2) := hsum
    _ = (E j).card + (E j).card * (ζ * A₀ / t) + (E j).card * (ζ * K) ^ 2 -
        ζ * ∑ γ ∈ E j, a j γ := hsplit
    _ ≤ (E j).card + (E j).card * (ζ * κ) + (E j).card * (ζ * m / 2) -
        ζ * (σ * (E j).card) := by linarith
    _ = (1 - ζ * m / 2) * (E j).card := by rw [hm]; ring

/-- (32): if the numbers of initial exponents grow like c j^n, the averages of |γ|/j are
eventually above every σ < (n/(n+1)) (n! c)^(1/n). -/
theorem eventually_average_degree_ge (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ)) {c : ℝ}
    (hc : 0 < c) (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    {σ : ℝ} (hσ : σ < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹) :
    ∀ᶠ j : ℕ in atTop, (E j).Nonempty ∧
      σ ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have hroot : Tendsto (fun j : ℕ => ((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^
      (n : ℝ)⁻¹) atTop (𝓝 (((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹)) :=
    (hN.const_mul _).rpow_const (Or.inr (by positivity))
  have hlow : Tendsto (fun j : ℕ => (n : ℝ) / (n + 1) * ((n.factorial : ℝ) *
      (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ - n / j) atTop
      (𝓝 ((n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹)) := by
    have h0 : Tendsto (fun j : ℕ => (n : ℝ) / j) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)
    simpa only [sub_zero] using (hroot.const_mul ((n : ℝ) / (n + 1))).sub h0
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < ((E j).card : ℝ) / (j : ℝ) ^ n :=
    hN.eventually_const_lt hc
  filter_upwards [hlow.eventually_const_lt hσ, hpos, eventually_ge_atTop 1] with j hj hposj hj1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hcard : (0 : ℝ) < (E j).card := by
    by_contra h
    have h0 : ((E j).card : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, zero_div] at hposj
    exact lt_irrefl 0 hposj
  have hne : (E j).Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  refine ⟨hne, ?_⟩
  have havg := average_degree_lower_bound n hn (E j) hne
  have hscale : ((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ =
      ((n.factorial : ℝ) * (E j).card) ^ (n : ℝ)⁻¹ / j := by
    rw [mul_div_assoc', Real.div_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hj0.le hn.ne']
  rw [hscale] at hj
  have hdiv : (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card =
      ((∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ)) / (E j).card) / j := by
    rw [← Finset.sum_div]
    ring
  rw [hdiv, le_div_iff₀ hj0]
  have h1 : ((n : ℝ) / (n + 1) * (((n.factorial : ℝ) * (E j).card) ^ (n : ℝ)⁻¹ / j) - n / j) * j =
      (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * (E j).card) ^ (n : ℝ)⁻¹ - n := by
    field_simp
  have h2 := mul_lt_mul_of_pos_right hj hj0
  rw [h1] at h2
  linarith

/-- The interior condition (7) at a smooth point (§7, and §8 after (33)): if the initial
exponents grow like c j^n with (n/(n+1)) (n! c)^(1/n) > n/b and have total degree at most C j,
then one t_0 < b, one ζ > 0 and one δ > 0 give
(1/N_j) Σ exp(ζ n/t - ζ |γ|/j) ≤ 1 - δ for all large j and all t ∈ [t_0, b]. -/
theorem interior_start_of_volume (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ))
    {c b C : ℝ} (hc : 0 < c) (hb : 0 < b) (hC : 0 ≤ C)
    (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    (hord : ∀ᶠ j : ℕ in atTop, ∀ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) ≤ C * j)
    (hvol : (n : ℝ) / b < (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t → t ≤ b →
      (∑ γ ∈ E j, Real.exp (ζ * n / t - ζ * (((∑ i, γ i : ℕ) : ℝ) / j))) / (E j).card ≤
        1 - δ := by
  set L := (n : ℝ) / (n + 1) * ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ with hL
  have hσ1 : (n : ℝ) / b < ((n : ℝ) / b + L) / 2 := by linarith
  have hσ2 : ((n : ℝ) / b + L) / 2 < L := by linarith
  have hev := eventually_average_degree_ge n hn E hc hN hσ2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine uniform_interior_start E (fun j γ => ((∑ i, γ i : ℕ) : ℝ) / j) hn0 hb hC hσ1
    (hev.mono fun j h => h.1) ?_ (hev.mono fun j h => h.2)
  filter_upwards [hord, eventually_ge_atTop 1] with j hj hj1 γ hγ
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  refine ⟨div_nonneg (Nat.cast_nonneg _) hj0.le, ?_⟩
  rw [div_le_iff₀ hj0]
  exact hj γ hγ

end MixedFujita
