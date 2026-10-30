/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
Rational points are dense in a polyhedron cut out by rational linear equalities and inequalities:
the choice of q^0 and c^0 in §6.1. Let x₀ be a real point of the polyhedron. The real numbers
1, x₀_1, ..., x₀_n span a finite-dimensional ℚ-subspace W of ℝ, and a ℚ-linear functional
g : W → ℚ with g(1) = 1 can be chosen as close to the identity on these finitely many numbers as
we like (approximate a ℚ-basis of W by rationals and normalize at 1). Then x = g(x₀) is
rational, satisfies every rational equality exactly (g commutes with rational linear
combinations and fixes the rationals), and satisfies every inequality that is active at x₀ as an
equality and every inactive one strictly once x is close to x₀. No Gaussian elimination, rank
comparison over field extensions, or vertex enumeration is needed.
-/

@[expose] public section

namespace MixedFujita

open Finset

/-- A ℚ-linear functional on a finite-dimensional ℚ-subspace of ℝ approximating the identity on
finitely many elements. -/
theorem exists_rat_functional_near_id (W : Submodule ℚ ℝ) [FiniteDimensional ℚ W] {ε : ℝ}
    (hε : 0 < ε) (S : Finset W) :
    ∃ g : W →ₗ[ℚ] ℚ, ∀ w ∈ S, |((g w : ℚ) : ℝ) - (w : ℝ)| < ε := by
  classical
  set b := Module.finBasis ℚ W with hb
  set T : ℝ := ∑ w ∈ S, ∑ k, |((b.repr w k : ℚ) : ℝ)| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  set δ : ℝ := ε / (1 + T) with hδ
  have hδ0 : 0 < δ := div_pos hε (by linarith)
  have hγ : ∀ k, ∃ q : ℚ, |(q : ℝ) - ((b k : W) : ℝ)| < δ := by
    intro k
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ((b k : W) : ℝ) - δ < ((b k : W) : ℝ) by linarith)
    refine ⟨q, ?_⟩
    rw [abs_lt]
    constructor <;> linarith
  choose γ hγ using hγ
  refine ⟨∑ k, γ k • b.coord k, fun w hw => ?_⟩
  have hgw : ((((∑ k, γ k • b.coord k) w : ℚ)) : ℝ) = ∑ k, ((b.repr w k : ℚ) : ℝ) * (γ k : ℝ) := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
      smul_eq_mul, Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hw' : (w : ℝ) = ∑ k, ((b.repr w k : ℚ) : ℝ) * ((b k : W) : ℝ) := by
    conv_lhs => rw [← b.sum_repr w]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Submodule.coe_smul, Rat.smul_def]
  rw [hgw, hw', ← Finset.sum_sub_distrib]
  have hbound : |∑ k, (((b.repr w k : ℚ) : ℝ) * (γ k : ℝ) -
      ((b.repr w k : ℚ) : ℝ) * ((b k : W) : ℝ))| ≤
      (∑ k, |((b.repr w k : ℚ) : ℝ)|) * δ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hγ k).le (abs_nonneg _)
  have hle : ∑ k, |((b.repr w k : ℚ) : ℝ)| ≤ T :=
    Finset.single_le_sum (f := fun w => ∑ k, |((b.repr w k : ℚ) : ℝ)|)
      (fun w _ => Finset.sum_nonneg fun k _ => abs_nonneg _) hw
  have hTδ : T * δ < ε := by
    rw [hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  calc _ ≤ (∑ k, |((b.repr w k : ℚ) : ℝ)|) * δ := hbound
    _ ≤ T * δ := mul_le_mul_of_nonneg_right hle hδ0.le
    _ < ε := hTδ

/-- The same with the normalization g(1) = 1. -/
theorem exists_rat_functional_one_near_id (W : Submodule ℚ ℝ) [FiniteDimensional ℚ W]
    (h1 : (1 : ℝ) ∈ W) {ε : ℝ} (hε : 0 < ε) (S : Finset W) :
    ∃ g : W →ₗ[ℚ] ℚ, g ⟨1, h1⟩ = 1 ∧ ∀ w ∈ S, |((g w : ℚ) : ℝ) - (w : ℝ)| < ε := by
  classical
  set M : ℝ := ∑ w ∈ S, |(w : ℝ)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun w _ => abs_nonneg _
  set ε' : ℝ := min (1 / 2) (ε / (2 * (1 + M))) with hε'
  have hε'0 : 0 < ε' := lt_min (by norm_num) (div_pos hε (by positivity))
  obtain ⟨g', hg'⟩ := exists_rat_functional_near_id W hε'0 (insert ⟨1, h1⟩ S)
  set c : ℚ := g' ⟨1, h1⟩ with hc
  have hc1 : |(c : ℝ) - 1| < ε' := by
    simpa using hg' ⟨1, h1⟩ (Finset.mem_insert_self _ _)
  have hε'half : ε' ≤ 1 / 2 := min_le_left _ _
  have hcpos : (1 : ℝ) / 2 < c := by
    rw [abs_lt] at hc1
    linarith
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero] at hcpos
    linarith
  refine ⟨c⁻¹ • g', ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, ← hc, smul_eq_mul, inv_mul_cancel₀ hc0]
  · have hw1 := hg' w (Finset.mem_insert_of_mem hw)
    have hwM : |(w : ℝ)| ≤ M :=
      Finset.single_le_sum (f := fun w : W => |(w : ℝ)|) (fun w _ => abs_nonneg _) hw
    have hcR : (0 : ℝ) < c := by linarith
    rw [LinearMap.smul_apply, smul_eq_mul, Rat.cast_mul, Rat.cast_inv]
    have hkey : (c : ℝ)⁻¹ * (g' w : ℝ) - (w : ℝ) =
        ((g' w : ℝ) - (w : ℝ) + (w : ℝ) * (1 - (c : ℝ))) / (c : ℝ) := by
      field_simp
      ring
    rw [hkey, abs_div, abs_of_pos hcR, div_lt_iff₀ hcR]
    have h2 : |(g' w : ℝ) - (w : ℝ) + (w : ℝ) * (1 - (c : ℝ))| ≤ ε' + M * ε' := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      have h3 : |1 - (c : ℝ)| < ε' := by rwa [abs_sub_comm]
      nlinarith [abs_nonneg (w : ℝ), abs_nonneg (1 - (c : ℝ))]
    have h4 : ε' * (1 + M) ≤ ε / 2 := by
      have h5 : ε' ≤ ε / (2 * (1 + M)) := min_le_right _ _
      calc ε' * (1 + M) ≤ ε / (2 * (1 + M)) * (1 + M) :=
            mul_le_mul_of_nonneg_right h5 (by linarith)
        _ = ε / 2 := by field_simp
    nlinarith

/-- §6.1: rational points are dense in a polyhedron given by rational equalities and
inequalities. -/
theorem exists_rat_near_polyhedron {n : ℕ} {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (A : κ₁ → Fin n → ℚ) (β : κ₁ → ℚ) (A' : κ₂ → Fin n → ℚ) (β' : κ₂ → ℚ)
    (x₀ : Fin n → ℝ) (heq : ∀ k, ∑ i, (A k i : ℝ) * x₀ i = β k)
    (hle : ∀ k, ∑ i, (A' k i : ℝ) * x₀ i ≤ β' k) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : Fin n → ℚ, (∀ k, ∑ i, A k i * x i = β k) ∧ (∀ k, ∑ i, A' k i * x i ≤ β' k) ∧
      ∀ i, |(x i : ℝ) - x₀ i| < ε := by
  classical
  set W : Submodule ℚ ℝ := Submodule.span ℚ (insert (1 : ℝ) (Set.range x₀)) with hW
  have hfin : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ ((Set.finite_range x₀).insert 1)
  have h1 : (1 : ℝ) ∈ W := Submodule.subset_span (Set.mem_insert _ _)
  have hx : ∀ i, x₀ i ∈ W := fun i =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  -- the accuracy needed for the inactive inequalities
  set L : ℝ := 1 + ∑ k, ∑ i, |((A' k i : ℚ) : ℝ)| with hL
  have hL0 : 0 < L := by
    have : 0 ≤ ∑ k, ∑ i, |((A' k i : ℚ) : ℝ)| :=
      Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  set inactive := Finset.univ.filter fun k => ∑ i, (A' k i : ℝ) * x₀ i < β' k
  set slack : ℝ := if h : inactive.Nonempty then
      inactive.inf' h (fun k => (β' k : ℝ) - ∑ i, (A' k i : ℝ) * x₀ i) else 1 with hslack
  have hslack0 : 0 < slack := by
    rw [hslack]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      intro k hk
      exact sub_pos.mpr (Finset.mem_filter.mp hk).2
    · exact one_pos
  set ε₁ : ℝ := min ε (slack / L) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε (div_pos hslack0 hL0)
  obtain ⟨g, hg1, hg⟩ := exists_rat_functional_one_near_id W h1 hε₁0
    (Finset.univ.image fun i => (⟨x₀ i, hx i⟩ : W))
  set x : Fin n → ℚ := fun i => g ⟨x₀ i, hx i⟩ with hxdef
  have hclose : ∀ i, |(x i : ℝ) - x₀ i| < ε₁ := fun i =>
    hg _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  -- g commutes with rational linear combinations
  have hcomb : ∀ a : Fin n → ℚ, ∀ r : ℚ, ∑ i, (a i : ℝ) * x₀ i = r → ∑ i, a i * x i = r := by
    intro a r hr
    have hmem : (∑ i, a i • (⟨x₀ i, hx i⟩ : W)) = r • (⟨1, h1⟩ : W) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, Rat.smul_def, mul_one]
      exact hr
    have h2 := congrArg g hmem
    rw [map_sum, map_smul, hg1, smul_eq_mul, mul_one] at h2
    simpa only [map_smul, smul_eq_mul, hxdef] using h2
  refine ⟨x, fun k => hcomb (A k) (β k) (heq k), fun k => ?_, fun i =>
    (hclose i).trans_le (min_le_left _ _)⟩
  by_cases hk : ∑ i, (A' k i : ℝ) * x₀ i < β' k
  · -- inactive: closeness keeps the strict inequality
    have hdev : |∑ i, (A' k i : ℝ) * (x i : ℝ) - ∑ i, (A' k i : ℝ) * x₀ i| <
        slack := by
      rw [← Finset.sum_sub_distrib]
      refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
      have hstep : ∀ i, |(A' k i : ℝ) * (x i : ℝ) - (A' k i : ℝ) * x₀ i| ≤
          |((A' k i : ℚ) : ℝ)| * ε₁ := by
        intro i
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hclose i).le (abs_nonneg _)
      have hsum : ∑ i, |((A' k i : ℚ) : ℝ)| ≤ L - 1 := by
        rw [hL, add_sub_cancel_left]
        exact Finset.single_le_sum (f := fun k => ∑ i, |((A' k i : ℚ) : ℝ)|)
          (fun k _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ k)
      calc ∑ i, |(A' k i : ℝ) * (x i : ℝ) - (A' k i : ℝ) * x₀ i|
          ≤ ∑ i, |((A' k i : ℚ) : ℝ)| * ε₁ := Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, |((A' k i : ℚ) : ℝ)|) * ε₁ := by rw [Finset.sum_mul]
        _ ≤ (L - 1) * ε₁ := mul_le_mul_of_nonneg_right hsum hε₁0.le
        _ < L * ε₁ := by linarith
        _ ≤ L * (slack / L) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL0.le
        _ = slack := by field_simp
    have hslk : slack ≤ (β' k : ℝ) - ∑ i, (A' k i : ℝ) * x₀ i := by
      have hkmem : k ∈ inactive := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have hne : inactive.Nonempty := ⟨k, hkmem⟩
      rw [hslack, dite_eq_left hne]
      exact Finset.inf'_le _ hkmem
    have hR : ∑ i, (A' k i : ℝ) * (x i : ℝ) < β' k := by
      rw [abs_lt] at hdev
      linarith
    exact_mod_cast hR.le
  · -- active: the inequality is an equality at x₀, preserved exactly
    have hact : ∑ i, (A' k i : ℝ) * x₀ i = β' k := le_antisymm (hle k) (not_lt.mp hk)
    exact (hcomb (A' k) (β' k) hact).le

/-- §6.1: the rational c^0 can be taken positive and with m Σ c^0 < b when the real c is positive
with m Σ c < b, the bound (25). -/
theorem exists_pos_rat_near_polyhedron {n : ℕ} {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (A : κ₁ → Fin n → ℚ) (β : κ₁ → ℚ) (A' : κ₂ → Fin n → ℚ) (β' : κ₂ → ℚ)
    (x₀ : Fin n → ℝ) (heq : ∀ k, ∑ i, (A k i : ℝ) * x₀ i = β k)
    (hle : ∀ k, ∑ i, (A' k i : ℝ) * x₀ i ≤ β' k) (hpos : ∀ i, 0 < x₀ i) {m b : ℝ} (hm : 0 ≤ m)
    (hb : m * ∑ i, x₀ i < b) :
    ∃ x : Fin n → ℚ, (∀ k, ∑ i, A k i * x i = β k) ∧ (∀ k, ∑ i, A' k i * x i ≤ β' k) ∧
      (∀ i, 0 < x i) ∧ m * ∑ i, (x i : ℝ) < b := by
  classical
  set μ : ℝ := if h : (Finset.univ : Finset (Fin n)).Nonempty then
    Finset.univ.inf' h x₀ else 1 with hμ
  have hμ0 : 0 < μ := by
    rw [hμ]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      exact fun i _ => hpos i
    · exact one_pos
  have hμle : ∀ i, μ ≤ x₀ i := by
    intro i
    have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ _⟩
    rw [hμ, dite_eq_left hne]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  set gap : ℝ := b - m * ∑ i, x₀ i with hgap
  have hgap0 : 0 < gap := sub_pos.mpr hb
  set ε : ℝ := min μ (gap / ((m + 1) * (n + 1))) with hε
  have hε0 : 0 < ε := lt_min hμ0 (div_pos hgap0 (by positivity))
  obtain ⟨x, hxeq, hxle, hclose⟩ := exists_rat_near_polyhedron A β A' β' x₀ heq hle hε0
  refine ⟨x, hxeq, hxle, fun i => ?_, ?_⟩
  · have h := hclose i
    rw [abs_lt] at h
    have h2 : ε ≤ μ := min_le_left _ _
    have h3 : (0 : ℝ) < x i := by linarith [hμle i]
    exact_mod_cast h3
  · have hdev : ∑ i, (x i : ℝ) - ∑ i, x₀ i ≤ n * ε := by
      rw [← Finset.sum_sub_distrib]
      calc ∑ i, ((x i : ℝ) - x₀ i) ≤ ∑ _i : Fin n, ε :=
            Finset.sum_le_sum fun i _ => (abs_lt.mp (hclose i)).2.le
        _ = n * ε := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hε2 : ε ≤ gap / ((m + 1) * (n + 1)) := min_le_right _ _
    have hmn : m * (n * ε) < gap := by
      have h1 : m * (n * ε) ≤ (m + 1) * (n + 1) * ε := by
        have := hε0.le
        nlinarith
      have h2 : (m + 1) * (n + 1) * ε ≤ gap := by
        calc (m + 1) * (n + 1) * ε ≤ (m + 1) * (n + 1) * (gap / ((m + 1) * (n + 1))) :=
              mul_le_mul_of_nonneg_left hε2 (by positivity)
          _ = gap := by field_simp
      have h3 : m * (n * ε) < (m + 1) * (n + 1) * ε ∨ m * (n * ε) = (m + 1) * (n + 1) * ε :=
        lt_or_eq_of_le h1
      rcases h3 with h3 | h3
      · linarith
      · nlinarith
    have : m * ∑ i, (x i : ℝ) ≤ m * ∑ i, x₀ i + m * (n * ε) := by
      have := mul_le_mul_of_nonneg_left hdev hm
      nlinarith
    linarith

end MixedFujita
