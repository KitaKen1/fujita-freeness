/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.MonomialIdealThresholdPoints

/-!
The threshold condition (34) on the exceptional divisor, along test valuations at every point of
every chart (§8), and its monomial case for exponents with the chart inequalities.

The exceptional divisor E of the blow-up of a smooth point of an n-dimensional variety is the
projective space with homogeneous coordinates x_1, …, x_n. In the chart x_k = 1, with the affine
coordinates x_i for i ≠ k, a point p and the coordinates y = x - p, a form g becomes the power
series g(x_k = 1, x_i = p_i + y_i) (`chartShiftedForm`). A test valuation at p is a K-algebra map
ψ of power series in the chart coordinates with ψ(y_i) ≠ 0 and det ∂ψ ≠ 0 (in characteristic
zero: ψ injective, so that v = w-order ∘ ψ is a valuation) and a nonzero weight w, with log
discrepancy A(v) = Σ w + v(det ∂ψ). The condition (34) for forms g_ℓ and an integer h
(`ProjectiveThresholdCondition`) is that along every such test valuation some g_ℓ has
v(g_ℓ) < h A(v): the threshold of the ideal of the g_ℓ on E exceeds 1/h at every point. Without
det ∂ψ ≠ 0 the condition would also test maps ψ with a kernel and would fail for forms with a
common non-coordinate zero curve, which is stronger than the threshold bound.

For monomials c_ℓ x^β_ℓ with c_ℓ ≠ 0 the condition holds as soon as, in every chart k and for every
nonzero natural weight u on the coordinates i ≠ k, some ℓ has Σ u_i β_ℓ,i < h Σ u_i
(`exists_shifted_monomial_lt_logDiscrepancy`). The real chart inequalities with a positive margin,
in the form produced for the sections of the equality case of Lemma 5, give these natural ones. So
the monomial degeneration of the leading forms of those sections satisfies (34); the passage to
the leading forms themselves is the degeneration of Lemma 3.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {K : Type*} [Field K] {n : ℕ}

/-- The form g in the chart x_k = 1 of projective space, in the coordinates y = x - p at the point
p of the chart, as a power series in the chart coordinates. -/
noncomputable def chartShiftedForm (k : Fin n) (p : {i : Fin n // i ≠ k} → K)
    (g : MvPolynomial (Fin n) K) : MvPowerSeries {i : Fin n // i ≠ k} K :=
  MvPolynomial.aeval (fun i : Fin n =>
    if h : i = k then (1 : MvPowerSeries {i : Fin n // i ≠ k} K) else C (p ⟨i, h⟩) + X ⟨i, h⟩) g

/-- A monomial in the chart x_k = 1 at the point p. -/
theorem chartShiftedForm_monomial (k : Fin n) (p : {i : Fin n // i ≠ k} → K)
    (β : Fin n →₀ ℕ) (c : K) :
    chartShiftedForm k p (MvPolynomial.monomial β c) =
      C c * ∏ i : {i : Fin n // i ≠ k}, (C (p i) + X i) ^ (β i) := by
  classical
  unfold chartShiftedForm
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), dite_eq_left rfl, one_pow, one_mul,
    Finset.prod_subtype (p := fun i => i ≠ k) (Finset.univ.erase k) (fun i => by simp)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [dite_eq_right i.property]

/-- The threshold condition (34) for forms g_ℓ and an integer h on the exceptional divisor: along
every test valuation (nonzero Jacobian determinant) at every point of every chart, some g_ℓ has
value smaller than h times the log discrepancy. -/
def ProjectiveThresholdCondition [DecidableEq K] {ι : Type*} (g : ι → MvPolynomial (Fin n) K)
    (h : ℕ) : Prop :=
  ∀ (k : Fin n) (p : {i : Fin n // i ≠ k} → K)
    (ψ : MvPowerSeries {i : Fin n // i ≠ k} K →ₐ[K] MvPowerSeries {i : Fin n // i ≠ k} K),
    (∀ i, ψ (X i) ≠ 0) → (powerSeriesJacobian ψ).det ≠ 0 → ∀ w : {i : Fin n // i ≠ k} → ℕ, w ≠ 0 →
      ∃ ℓ, (ψ (chartShiftedForm k p (g ℓ))).weightedOrder w <
        (h : ℕ∞) * (((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w)

/-- The monomial case of (34) in every chart: monomials c_ℓ x^β_ℓ with c_ℓ ≠ 0 whose exponents
satisfy the natural chart inequalities. -/
theorem projectiveThresholdCondition_monomial [DecidableEq K] {ι : Type*} [Nonempty ι]
    (β : ι → (Fin n →₀ ℕ)) (c : ι → K) (hc : ∀ ℓ, c ℓ ≠ 0) (h : ℕ) (hh : 1 ≤ h)
    (hβ : ∀ (k : Fin n) (u : {i : Fin n // i ≠ k} → ℕ), u ≠ 0 →
      ∃ ℓ, ∑ i, u i * β ℓ i < h * ∑ i, u i) :
    ProjectiveThresholdCondition (fun ℓ => MvPolynomial.monomial (β ℓ) (c ℓ)) h := by
  intro k p ψ hψ _ w hw
  obtain ⟨ℓ, hℓ⟩ := exists_shifted_monomial_lt_logDiscrepancy ψ
    (fun ℓ => (β ℓ).subtypeDomain (· ≠ k)) h hh
    (fun u hu => by
      obtain ⟨ℓ, hℓ⟩ := hβ k u hu
      exact ⟨ℓ, by simpa only [Finsupp.subtypeDomain_apply] using hℓ⟩) p hψ w hw
  refine ⟨ℓ, ?_⟩
  have hC : (ψ (C (c ℓ))).weightedOrder w = 0 := by
    rw [show (C (c ℓ) : MvPowerSeries {i : Fin n // i ≠ k} K) =
      algebraMap K (MvPowerSeries {i : Fin n // i ≠ k} K) (c ℓ) from rfl, AlgHom.commutes]
    exact weightedOrder_eq_zero_of_isUnit w ((isUnit_iff_ne_zero.mpr (hc ℓ)).map _)
  simp only [chartShiftedForm_monomial, map_mul, weightedOrder_mul, hC, zero_add]
  simpa only [Finsupp.subtypeDomain_apply] using hℓ

/-- Real chart inequalities with a positive margin give the natural chart inequalities of the
monomial case of (34). -/
theorem chart_inequalities_nat_of_margin {L : Type*} (β : L → Fin n →₀ ℕ) (pick : Fin n → Fin n → L)
    {H : ℕ} (hH : 1 ≤ H) {μ : ℝ} (hμ : 0 < μ)
    (hmargin : ∀ (w : Fin n → ℝ) (k : Fin n), w k = 0 → ∃ i : Fin n,
      (∑ q, w q * (β (pick k i) q : ℝ)) ≤ (H : ℝ) * (1 - μ) * (∑ q, w q))
    (k : Fin n) (u : {i : Fin n // i ≠ k} → ℕ) (hu : u ≠ 0) :
    ∃ ℓ, ∑ j, u j * β ℓ j < H * ∑ j, u j := by
  classical
  set w : Fin n → ℝ := fun q => if h : q = k then 0 else (u ⟨q, h⟩ : ℝ) with hw
  have hwk : w k = 0 := by simp [hw]
  obtain ⟨i, hi⟩ := hmargin w k hwk
  refine ⟨pick k i, ?_⟩
  have hsub : ∀ F : Fin n → ℝ, (∀ q, q = k → F q = 0) →
      ∑ q, F q = ∑ j : {i : Fin n // i ≠ k}, F j := by
    intro F hF
    rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ k), hF k rfl, zero_add,
      Finset.sum_subtype (p := fun i => i ≠ k) (Finset.univ.erase k) (fun i => by simp)]
  have h1 : ∑ q, w q * (β (pick k i) q : ℝ) = ∑ j : {i : Fin n // i ≠ k},
      (u j : ℝ) * (β (pick k i) j : ℝ) := by
    rw [hsub _ (fun q hq => by simp [hw, hq])]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hw, j.property]
  have h2 : ∑ q, w q = ∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) := by
    rw [hsub _ (fun q hq => by simp [hw, hq])]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hw, j.property]
  have hupos : (0 : ℝ) < ∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) := by
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    have hj' : (0 : ℝ) < u j := by exact_mod_cast Nat.pos_of_ne_zero hj
    exact lt_of_lt_of_le hj' (Finset.single_le_sum (fun j _ => Nat.cast_nonneg (u j))
      (Finset.mem_univ j))
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  rw [h1, h2] at hi
  have hlt : (∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) * (β (pick k i) j : ℝ)) <
      (H : ℝ) * ∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) := by
    have : (H : ℝ) * (1 - μ) * ∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) <
        (H : ℝ) * ∑ j : {i : Fin n // i ≠ k}, (u j : ℝ) := by
      have := mul_pos hH' hupos
      nlinarith
    linarith
  exact_mod_cast hlt

/-- Monomials whose exponents satisfy real chart inequalities with a positive margin satisfy the
threshold condition (34) on the exceptional divisor. -/
theorem projectiveThresholdCondition_monomial_of_margin [DecidableEq K] (hn : 0 < n)
    (β : Fin n × Fin n → Fin n →₀ ℕ) (c : Fin n × Fin n → K) (hc : ∀ l, c l ≠ 0)
    {H : ℕ} (hH : 1 ≤ H) {μ : ℝ} (hμ : 0 < μ)
    (hmargin : ∀ (w : Fin n → ℝ) (k : Fin n), w k = 0 → ∃ i : Fin n,
      (∑ q, w q * (β (k, i) q : ℝ)) ≤ (H : ℝ) * (1 - μ) * (∑ q, w q)) :
    ProjectiveThresholdCondition (fun l => MvPolynomial.monomial (β l) (c l)) H := by
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  exact projectiveThresholdCondition_monomial β c hc H hH
    (fun k u hu => chart_inequalities_nat_of_margin β (fun k i => (k, i)) hH hμ hmargin k u hu)

end MixedFujita
