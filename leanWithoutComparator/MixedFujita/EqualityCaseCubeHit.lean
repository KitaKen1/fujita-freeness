/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EqualityCaseDichotomy
public import MixedFujita.SimplexMoment

/-!
The equality case of Lemma 5 (§8): the initial exponents meet every small cube inside the simplex
(the first step of the proof of (33)).

Let E_j ⊂ ℕ^n have about c j^n points with n! c = (n + 1)^n, so that E_j has as many points as
the simplex {|γ| ≤ (n + 1) j} up to o(j^n). Suppose E_j avoids the lattice points of j Q for a cube
Q = Π [a_i, a_i + ρ] with Σ (a_i + ρ) = n + 1 - ε. Those are at least (ρ j - 1)^n points of total
degree at most (n + 1 - ε) j, so from that degree on the number of points of E_j of shifted degree
below t is at most the stars-and-bars bound minus (ρ j - 1)^n. Integrating the cumulative count as
in the simplex moment bound gives an extra (ρ j - 1)^n (R - (n + 1 - ε) j - n) in Σ (|γ| + n), with
R = (n! |E_j|)^(1/n) ~ (n + 1) j. So the average of |γ|/j is at least n + ε ρ^n/c - o(1).

Hence, in the equality branch of `equality_case_dichotomy` (the means are frequently at most
n + ε for every ε > 0), the sets E_j/j frequently meet finitely many given cubes inside the
simplex at once.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology MeasureTheory

/-- If E avoids a finite set C of lattice points whose shifted total degrees are at most t₁, its
cumulative count of shifted total degrees drops by |C| from t₁ on. -/
theorem lattice_cumulativeCount_bound_of_disjoint (n : ℕ) (E C : Finset (Fin n → ℕ))
    (hEC : Disjoint E C) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hC : ∀ γ ∈ C, (((∑ i, γ i) + n : ℕ) : ℝ) ≤ t₁) {t : ℝ} (ht : t₁ ≤ t) :
    cumulativeCount E (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ)) t ≤
      t ^ n / (n.factorial : ℝ) - C.card := by
  classical
  have ht0 : 0 ≤ t := ht₁.trans ht
  set m := ⌊t⌋₊ with hm
  set S : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.range (m + 1)) with hS
  have hdeg : ∀ γ : Fin n → ℕ, (∑ i, γ i) + n ≤ m →
      γ ∈ S.filter (fun γ => (∑ i, γ i) + n ≤ m) := by
    intro γ hγ
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => Finset.mem_range.mpr ?_, hγ⟩
    have : γ i ≤ ∑ i, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hA : E.filter (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ) < t) ⊆
      S.filter (fun γ => (∑ i, γ i) + n ≤ m) := by
    intro γ hγ
    obtain ⟨-, hγ⟩ := Finset.mem_filter.mp hγ
    exact hdeg γ ((Nat.le_floor_iff ht0).mpr hγ.le)
  have hC' : C ⊆ S.filter (fun γ => (∑ i, γ i) + n ≤ m) := by
    intro γ hγ
    exact hdeg γ ((Nat.le_floor_iff ht0).mpr ((hC γ hγ).trans ht))
  have hdisj : Disjoint (E.filter (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ) < t)) C :=
    hEC.mono_left (Finset.filter_subset _ _)
  have hcard : (E.filter (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ) < t)).card + C.card ≤
      m.choose n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card (Finset.union_subset hA hC')).trans
      (lattice_cost_count_bound n m S)
  have hchoose : (m.choose n : ℝ) ≤ t ^ n / (n.factorial : ℝ) :=
    (Nat.choose_le_pow_div n m).trans (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le ht0) n) (by positivity))
  have h1 : ((E.filter (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ) < t)).card : ℝ) + C.card ≤
      m.choose n := by
    exact_mod_cast hcard
  unfold cumulativeCount
  linarith

/-- The moment bound of `finite_moment_lower_bound_of_count` when the count drops by M from t₁
on: an extra M (R - t₁). -/
theorem finite_moment_lower_bound_of_count_gap {ι : Type*} (E : Finset ι) (c : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ E, 0 ≤ c i) {M t₁ R : ℝ} (ht₁ : 0 ≤ t₁) (hR : t₁ ≤ R)
    (hcount : ∀ t ≥ 0, cumulativeCount E c t ≤ t ^ n / (n.factorial : ℝ))
    (hgap : ∀ t ≥ t₁, cumulativeCount E c t ≤ t ^ n / (n.factorial : ℝ) - M) :
    R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) + M * (R - t₁) ≤
      ∑ i ∈ E, c i := by
  have hR0 : 0 ≤ R := ht₁.trans hR
  have hsum : R * (E.card : ℝ) - ∑ i ∈ E, c i ≤ ∫ t in (0 : ℝ)..R, cumulativeCount E c t := by
    rw [integral_cumulativeCount E c hc hR0]
    calc
      _ = ∑ i ∈ E, (R - c i) := by
        rw [Finset.sum_sub_distrib]
        simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun _ _ => le_max_right _ _)
  have hint0 := cumulativeCount_intervalIntegrable E c t₁
  have hintR := cumulativeCount_intervalIntegrable E c R
  have hint1 : IntervalIntegrable (cumulativeCount E c) volume t₁ R := hint0.symm.trans hintR
  have hpoly_int : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t ^ n / (n.factorial : ℝ)) volume a b :=
    fun a b => ((continuous_id.pow n).div_const (n.factorial : ℝ)).intervalIntegrable a b
  have hsplit : (∫ t in (0 : ℝ)..R, cumulativeCount E c t) =
      (∫ t in (0 : ℝ)..t₁, cumulativeCount E c t) + ∫ t in t₁..R, cumulativeCount E c t :=
    (intervalIntegral.integral_add_adjacent_intervals hint0 hint1).symm
  have hle0 : (∫ t in (0 : ℝ)..t₁, cumulativeCount E c t) ≤
      ∫ t in (0 : ℝ)..t₁, t ^ n / (n.factorial : ℝ) :=
    intervalIntegral.integral_mono_on ht₁ hint0 (hpoly_int 0 t₁) (fun t ht => hcount t ht.1)
  have hle1 : (∫ t in t₁..R, cumulativeCount E c t) ≤
      ∫ t in t₁..R, (t ^ n / (n.factorial : ℝ) - M) :=
    intervalIntegral.integral_mono_on hR hint1 ((hpoly_int t₁ R).sub intervalIntegrable_const)
      (fun t ht => hgap t ht.1)
  have heq1 : (∫ t in t₁..R, (t ^ n / (n.factorial : ℝ) - M)) =
      (∫ t in t₁..R, t ^ n / (n.factorial : ℝ)) - M * (R - t₁) := by
    rw [intervalIntegral.integral_sub (hpoly_int t₁ R) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hpoly_split : (∫ t in (0 : ℝ)..t₁, t ^ n / (n.factorial : ℝ)) +
      (∫ t in t₁..R, t ^ n / (n.factorial : ℝ)) =
      ∫ t in (0 : ℝ)..R, t ^ n / (n.factorial : ℝ) :=
    intervalIntegral.integral_add_adjacent_intervals (hpoly_int 0 t₁) (hpoly_int t₁ R)
  have hpoly : (∫ t in (0 : ℝ)..R, t ^ n / (n.factorial : ℝ)) =
      R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) := by
    rw [intervalIntegral.integral_div, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero _), sub_zero]
    rw [div_div]
  linarith

/-- The simplex moment bound for lattice points avoiding a finite set C of lattice points of
shifted total degree at most t₁ ≤ R, R = (n! |E|)^(1/n): an extra |C| (R - t₁). -/
theorem simplex_moment_lower_bound_of_disjoint (n : ℕ) (hn : 0 < n) (E C : Finset (Fin n → ℕ))
    (hEC : Disjoint E C) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    (hC : ∀ γ ∈ C, (((∑ i, γ i) + n : ℕ) : ℝ) ≤ t₁)
    (hR : t₁ ≤ ((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹) :
    (n : ℝ) / (n + 1 : ℝ) * ((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹ * E.card +
        C.card * (((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹ - t₁) ≤
      ∑ γ ∈ E, (((∑ i, γ i) + n : ℕ) : ℝ) := by
  set R : ℝ := ((n.factorial : ℝ) * (E.card : ℝ)) ^ (n : ℝ)⁻¹ with hRdef
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hRn : R ^ n = (n.factorial : ℝ) * (E.card : ℝ) := by
    rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hn',
      Real.rpow_one]
  have hg := finite_moment_lower_bound_of_count_gap E (fun γ => (((∑ i, γ i) + n : ℕ) : ℝ)) n
    (fun _ _ => by positivity) (M := (C.card : ℝ)) ht₁ hR
    (fun _ ht => lattice_cumulativeCount_bound n E ht)
    (fun t ht => lattice_cumulativeCount_bound_of_disjoint n E C hEC ht₁ hC ht)
  have hpow : R ^ (n + 1) = R * (n.factorial : ℝ) * (E.card : ℝ) := by
    rw [pow_succ, hRn]
    ring
  have hfirst : R * (E.card : ℝ) - R ^ (n + 1) / ((n + 1 : ℝ) * (n.factorial : ℝ)) =
      (n : ℝ) / (n + 1 : ℝ) * R * E.card := by
    rw [hpow]
    field_simp
    ring
  linarith

/-- The number of integers in [x, y] is at least y - x - 1 when 0 ≤ x and x + 1 ≤ y. -/
theorem card_Icc_ceil_floor_ge {x y : ℝ} (hx : 0 ≤ x) (hxy : x + 1 ≤ y) :
    y - x - 1 ≤ ((Finset.Icc ⌈x⌉₊ ⌊y⌋₊).card : ℝ) := by
  rw [Nat.card_Icc]
  have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have h3 : ⌈x⌉₊ ≤ ⌊y⌋₊ + 1 := by
    have : (⌈x⌉₊ : ℝ) ≤ ⌊y⌋₊ + 1 := by linarith
    exact_mod_cast this
  rw [Nat.cast_sub h3]
  push_cast
  linarith

/-- The equality case of Lemma 5: a set of initial exponents missing the lattice points of j Q,
for a cube Q inside the simplex, has average total degree above n + η. -/
theorem equality_case_cube_gap (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ)) {c : ℝ}
    (hc : 0 < c) (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    (hvol : (n.factorial : ℝ) * c = ((n + 1 : ℕ) : ℝ) ^ n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) {ρ : ℝ} (hρ : 0 < ρ)
    (hcube : ∑ i, (a i + ρ) < n + 1) :
    ∃ η > 0, ∀ᶠ j : ℕ in atTop,
      (∀ γ ∈ E j, ¬ ∀ i, a i * j ≤ γ i ∧ (γ i : ℝ) ≤ (a i + ρ) * j) →
        n + η ≤ (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card := by
  classical
  set ε : ℝ := n + 1 - ∑ i, (a i + ρ) with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hsum0 : 0 ≤ ∑ i, (a i + ρ) := Finset.sum_nonneg fun i _ => by linarith [ha i]
  refine ⟨ε * ρ ^ n / c / 2, by positivity, ?_⟩
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  -- the limits
  have hroot : Tendsto (fun j : ℕ => ((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^
      (n : ℝ)⁻¹) atTop (𝓝 ((n : ℝ) + 1)) := by
    have h := (hN.const_mul (n.factorial : ℝ)).rpow_const (p := (n : ℝ)⁻¹)
      (Or.inr (by positivity))
    have hval : ((n.factorial : ℝ) * c) ^ (n : ℝ)⁻¹ = (n : ℝ) + 1 := by
      rw [hvol, Real.pow_rpow_inv_natCast (by positivity) hn.ne']
      push_cast
      ring
    rwa [hval] at h
  have h1j : Tendsto (fun j : ℕ => (1 : ℝ) / j) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hnj : Tendsto (fun j : ℕ => (n : ℝ) / j) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (n : ℝ)
  have hm : Tendsto (fun j : ℕ => (ρ - 1 / j) ^ n / (((E j).card : ℝ) / (j : ℝ) ^ n)) atTop
      (𝓝 (ρ ^ n / c)) := by
    have h := (((tendsto_const_nhds (x := ρ)).sub h1j).pow n).div hN hc.ne'
    rw [sub_zero] at h
    exact h
  have hlim : Tendsto (fun j : ℕ => (n : ℝ) / (n + 1) * ((n.factorial : ℝ) *
      (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ - n / j +
      (ρ - 1 / j) ^ n / (((E j).card : ℝ) / (j : ℝ) ^ n) *
        (((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ -
          ((n + 1 - ε) + n / j))) atTop
      (𝓝 ((n : ℝ) / (n + 1) * ((n : ℝ) + 1) - 0 +
        ρ ^ n / c * (((n : ℝ) + 1) - ((n + 1 - ε) + 0)))) :=
    ((hroot.const_mul _).sub hnj).add (hm.mul (hroot.sub (tendsto_const_nhds.add hnj)))
  have hval : (n : ℝ) / (n + 1) * ((n : ℝ) + 1) - 0 +
      ρ ^ n / c * (((n : ℝ) + 1) - ((n + 1 - ε) + 0)) = n + ε * ρ ^ n / c := by
    field_simp
    ring
  rw [hval] at hlim
  have hlt : (n : ℝ) + ε * ρ ^ n / c / 2 < n + ε * ρ ^ n / c := by
    have : 0 < ε * ρ ^ n / c := by positivity
    linarith
  have hthr : Tendsto (fun j : ℕ => (n + 1 - ε) + (n : ℝ) / j) atTop (𝓝 ((n + 1 - ε) + 0)) :=
    tendsto_const_nhds.add hnj
  have hrlt : ((n : ℝ) + 1 - ε) + 0 < (n : ℝ) + 1 := by linarith
  have hρj : ∀ᶠ j : ℕ in atTop, 1 ≤ ρ * j := by
    obtain ⟨k, hk⟩ := exists_nat_ge (1 / ρ)
    filter_upwards [eventually_ge_atTop k] with j hj
    have hkj : (k : ℝ) ≤ j := by exact_mod_cast hj
    have h := mul_le_mul_of_nonneg_left (hk.trans hkj) hρ.le
    rwa [mul_one_div_cancel hρ.ne'] at h
  have hpos : ∀ᶠ j : ℕ in atTop, 0 < ((E j).card : ℝ) / (j : ℝ) ^ n :=
    hN.eventually_const_lt hc
  have hRge : ∀ᶠ j : ℕ in atTop, (n + 1 - ε) + (n : ℝ) / j ≤
      ((n.factorial : ℝ) * (((E j).card : ℝ) / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ := by
    obtain ⟨u, hu1, hu2⟩ := exists_between hrlt
    filter_upwards [hthr.eventually_lt_const hu1, hroot.eventually_const_lt hu2] with j h1 h2
    linarith
  filter_upwards [hlim.eventually_const_lt hlt, hρj, hpos, hRge, eventually_ge_atTop 1]
    with j hj hρj hposj hRj hj1 hmiss
  -- notation
  set N : ℝ := ((E j).card : ℝ) with hNdef
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hN0 : 0 < N := by
    by_contra h
    have h0 : N = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, zero_div] at hposj
    exact lt_irrefl 0 hposj
  set r : ℝ := ((n.factorial : ℝ) * (N / (j : ℝ) ^ n)) ^ (n : ℝ)⁻¹ with hr
  have hscale : r = ((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ / j := by
    rw [hr, mul_div_assoc', Real.div_rpow (by positivity) (by positivity),
      Real.pow_rpow_inv_natCast hj0.le hn.ne']
  -- the lattice points of the cube
  set C : Finset (Fin n → ℕ) := Fintype.piFinset
    (fun i => Finset.Icc ⌈a i * j⌉₊ ⌊(a i + ρ) * j⌋₊) with hCdef
  have hmemC : ∀ γ ∈ C, ∀ i, a i * j ≤ γ i ∧ (γ i : ℝ) ≤ (a i + ρ) * j := by
    intro γ hγ i
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hγ i)
    exact ⟨Nat.ceil_le.mp h1, (Nat.le_floor_iff (by positivity [ha i])).mp h2⟩
  have hEC : Disjoint (E j) C :=
    Finset.disjoint_left.mpr fun γ hγE hγC => hmiss γ hγE (hmemC γ hγC)
  set t₁ : ℝ := (n + 1 - ε) * j + n with ht₁def
  have ht₁0 : 0 ≤ t₁ := by
    have : 0 ≤ (n : ℝ) + 1 - ε := by rw [hε]; linarith
    positivity
  have hdegC : ∀ γ ∈ C, (((∑ i, γ i) + n : ℕ) : ℝ) ≤ t₁ := by
    intro γ hγ
    have h1 : ((∑ i, γ i : ℕ) : ℝ) ≤ ∑ i, (a i + ρ) * j := by
      push_cast
      exact Finset.sum_le_sum fun i _ => (hmemC γ hγ i).2
    rw [← Finset.sum_mul] at h1
    have h2 : ∑ i, (a i + ρ) = (n : ℝ) + 1 - ε := by rw [hε]; ring
    rw [h2] at h1
    rw [ht₁def]
    push_cast
    push_cast at h1
    linarith
  have hRt : t₁ ≤ ((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hRj hj0.le
    rw [hscale, div_mul_cancel₀ _ hj0.ne'] at h
    rw [ht₁def]
    have hexp : ((n : ℝ) + 1 - ε + (n : ℝ) / j) * j = ((n : ℝ) + 1 - ε) * j + n := by
      field_simp
    linarith [hexp]
  -- the count of the cube
  have hCcard : (ρ * j - 1) ^ n ≤ (C.card : ℝ) := by
    rw [hCdef, Fintype.card_piFinset]
    push_cast
    have hfac : ∀ i ∈ Finset.univ, 0 ≤ ρ * j - 1 ∧
        ρ * j - 1 ≤ ((Finset.Icc ⌈a i * j⌉₊ ⌊(a i + ρ) * j⌋₊).card : ℝ) := by
      intro i _
      refine ⟨by linarith, ?_⟩
      have h := card_Icc_ceil_floor_ge (x := a i * j) (y := (a i + ρ) * j)
        (by positivity [ha i]) (by nlinarith)
      have hxy : (a i + ρ) * j - a i * j - 1 = ρ * j - 1 := by ring
      rwa [hxy] at h
    calc (ρ * j - 1) ^ n = ∏ _i : Fin n, (ρ * j - 1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)
  -- the simplex moment bound with the gap
  have hS := simplex_moment_lower_bound_of_disjoint n hn (E j) C hEC ht₁0 hdegC hRt
  have hsumE : ∑ γ ∈ E j, (((∑ i, γ i) + n : ℕ) : ℝ) =
      (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ)) + n * N := by
    simp only [Nat.cast_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hNdef]
    ring
  rw [hsumE, ← hNdef] at hS
  -- the comparison with the limit
  have hRr : ((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ = r * j := by
    rw [hscale, div_mul_cancel₀ _ hj0.ne']
  have hgap0 : 0 ≤ ((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ - t₁ := by linarith
  have hCgap : (ρ * j - 1) ^ n * (((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ - t₁) ≤
      C.card * (((n.factorial : ℝ) * N) ^ (n : ℝ)⁻¹ - t₁) :=
    mul_le_mul_of_nonneg_right hCcard hgap0
  have hkey : ((n : ℝ) / (n + 1) * r - n / j + (ρ - 1 / j) ^ n / (N / (j : ℝ) ^ n) *
      (r - ((n + 1 - ε) + n / j))) * (j * N) ≤ ∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) := by
    have hpowj : (ρ - 1 / j) ^ n * (j : ℝ) ^ n = (ρ * j - 1) ^ n := by
      rw [← mul_pow, sub_mul, one_div_mul_cancel hj0.ne']
    have hmN : (ρ - 1 / j) ^ n / (N / (j : ℝ) ^ n) * N = (ρ - 1 / j) ^ n * (j : ℝ) ^ n := by
      rw [div_div_eq_mul_div, div_mul_cancel₀ _ hN0.ne']
    have hq : ((n : ℝ) + 1 - ε + n / j) * j = t₁ := by
      rw [ht₁def, add_mul, div_mul_cancel₀ _ hj0.ne']
    have hnj' : (n : ℝ) / j * j = n := div_mul_cancel₀ _ hj0.ne'
    have hexpand : ((n : ℝ) / (n + 1) * r - n / j + (ρ - 1 / j) ^ n / (N / (j : ℝ) ^ n) *
        (r - ((n + 1 - ε) + n / j))) * (j * N) =
        (n : ℝ) / (n + 1) * (r * j) * N - n * N +
          (ρ - 1 / j) ^ n * (j : ℝ) ^ n * (r * j - t₁) := by
      linear_combination ((r - ((n + 1 - ε) + n / j)) * j) * hmN +
        (-((ρ - 1 / j) ^ n * (j : ℝ) ^ n)) * hq + (-N) * hnj'
    rw [hexpand, hpowj, ← hRr]
    linarith [hS, hCgap]
  have havg : (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card =
      (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ)) / (j * N) := by
    rw [← Finset.sum_div, hNdef, div_div]
  rw [havg, le_div_iff₀ (mul_pos hj0 hN0)]
  have hj' := hj
  calc ((n : ℝ) + ε * ρ ^ n / c / 2) * (j * N) ≤
        ((n : ℝ) / (n + 1) * r - n / j + (ρ - 1 / j) ^ n / (N / (j : ℝ) ^ n) *
          (r - ((n + 1 - ε) + n / j))) * (j * N) :=
        mul_le_mul_of_nonneg_right hj'.le (mul_pos hj0 hN0).le
    _ ≤ _ := hkey

/-- In the equality case, if the means of |γ|/j are frequently at most n + ε for every ε > 0, the
sets E_j frequently meet finitely many given cubes inside the simplex at once. -/
theorem equality_case_frequently_meets_cubes (n : ℕ) (hn : 0 < n) (E : ℕ → Finset (Fin n → ℕ))
    {c : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun j : ℕ => ((E j).card : ℝ) / (j : ℝ) ^ n) atTop (𝓝 c))
    (hvol : (n.factorial : ℝ) * c = ((n + 1 : ℕ) : ℝ) ^ n)
    (hmean : ∀ ε > 0, ∃ᶠ j : ℕ in atTop,
      (∑ γ ∈ E j, ((∑ i, γ i : ℕ) : ℝ) / j) / (E j).card ≤ n + ε)
    {K : ℕ} (a : Fin K → Fin n → ℝ) (ha : ∀ k i, 0 ≤ a k i) {ρ : ℝ} (hρ : 0 < ρ)
    (hcube : ∀ k, ∑ i, (a k i + ρ) < n + 1) :
    ∃ᶠ j : ℕ in atTop, ∀ k, ∃ γ ∈ E j, ∀ i, a k i * j ≤ γ i ∧ (γ i : ℝ) ≤ (a k i + ρ) * j := by
  choose η hη hev using fun k => equality_case_cube_gap n hn E hc hN hvol (a k) (ha k) hρ (hcube k)
  obtain ⟨η₀, hη₀, hη₀le⟩ : ∃ η₀ > 0, ∀ k, η₀ ≤ η k := by
    by_cases hK : K = 0
    · exact ⟨1, one_pos, fun k => absurd k.2 (by omega)⟩
    · have : Nonempty (Fin K) := ⟨⟨0, Nat.pos_of_ne_zero hK⟩⟩
      obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ η Finset.univ_nonempty
      exact ⟨η k₀, hη k₀, fun k => hk₀ k (Finset.mem_univ k)⟩
  have hall := Filter.eventually_all.mpr hev
  refine ((hmean (η₀ / 2) (by positivity)).and_eventually hall).mono ?_
  rintro j ⟨hj, hallj⟩ k
  by_contra hno
  have h := hallj k (fun γ hγ hγQ => hno ⟨γ, hγ, hγQ⟩)
  linarith [hη₀le k]

end MixedFujita
