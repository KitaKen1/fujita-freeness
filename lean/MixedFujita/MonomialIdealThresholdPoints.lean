/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCDiscrepancyInequality
public import MixedFujita.GeometricJacobianBound

/-!
The monomial case of (34) at every point of a chart of E, and for generators with given monomials.
At a point p of the chart, in the coordinates y = x - p, the monomial x^β is Π_i (p_i + y_i)^β_i;
the factors with p_i ≠ 0 are units, so a test valuation v (a map ψ and weights w in the coordinates
y) has v(x^β) = Σ_{p_i = 0} β_i v(y_i). With a_i = v(y_i) for p_i = 0 and a_i = 0 otherwise, the
condition min_ℓ ⟨u, β_ℓ⟩ < h Σ u_i for all nonzero weights u, applied to a, and the SNC
discrepancy inequality Σ_i v(y_i) ≤ A(v) give a generator with v(x^β_ℓ) < h A(v): the threshold
of the monomial ideal exceeds 1/h along every test valuation centred at any point of the chart,
not only at the torus-fixed point. For generators g_ℓ having the monomial x^β_ℓ, monomial
valuations in the coordinates x itself satisfy v_w(g_ℓ) ≤ ⟨w, β_ℓ⟩, so the same holds for the
original ideal along these valuations; the remaining valuations of (34) are handled by the
degeneration of Lemma 3.
-/

@[expose] public section

namespace MixedFujita

open MvPowerSeries

variable {σ K : Type*} [Field K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
  (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)

omit [Fintype σ] [DecidableEq σ] in
/-- The value of a coordinate of the chart in the coordinates y = x - p. -/
theorem weightedOrder_algHom_C_add_X (w : σ → ℕ) (p : σ → K) (i : σ) :
    (ψ (C (p i) + X i)).weightedOrder w =
      if p i = 0 then (ψ (X i)).weightedOrder w else 0 := by
  by_cases hp : p i = 0
  · rw [ite_eq_left hp, hp, map_zero, zero_add]
  · rw [ite_eq_right hp]
    have hu : IsUnit (C (p i) + X i : MvPowerSeries σ K) := by
      rw [isUnit_iff_constantCoeff, map_add, constantCoeff_C, constantCoeff_X, add_zero]
      exact (Ne.isUnit hp)
    exact weightedOrder_eq_zero_of_isUnit w (hu.map ψ)

omit [DecidableEq σ] in
/-- The value of the monomial x^β in the coordinates at p. -/
theorem weightedOrder_algHom_shifted_monomial (w : σ → ℕ) (p : σ → K) (β : σ →₀ ℕ) :
    (ψ (∏ i, (C (p i) + X i) ^ (β i))).weightedOrder w =
      ∑ i, β i • (if p i = 0 then (ψ (X i)).weightedOrder w else 0) := by
  rw [map_prod, weightedOrder_prod]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, ← weightedOrder_algHom_C_add_X ψ w p i]
  induction β i with
  | zero => simp
  | succ k ih => rw [pow_succ, weightedOrder_mul, ih, succ_nsmul]

/-- The monomial case of (34) at any point p of the chart. -/
theorem exists_shifted_monomial_lt_logDiscrepancy {ι : Type*} [Nonempty ι] (β : ι → (σ →₀ ℕ))
    (h : ℕ) (hh : 1 ≤ h) (hβ : ∀ u : σ → ℕ, u ≠ 0 → ∃ ℓ, ∑ i, u i * β ℓ i < h * ∑ i, u i)
    (p : σ → K) (hψ : ∀ i, ψ (X i) ≠ 0) (w : σ → ℕ) (hw : w ≠ 0) :
    ∃ ℓ, (ψ (∏ i, (C (p i) + X i) ^ (β ℓ i))).weightedOrder w <
      (h : ℕ∞) * (((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) := by
  set a : σ → ℕ := fun i => ((ψ (X i)).weightedOrder w).toNat with ha
  have hfin : ∀ i, ((ψ (X i)).weightedOrder w) = (a i : ℕ∞) := fun i =>
    ((ne_zero_iff_weightedOrder_finite w).mp (hψ i)).symm
  set a' : σ → ℕ := fun i => if p i = 0 then a i else 0 with ha'
  have hval : ∀ ℓ, (ψ (∏ i, (C (p i) + X i) ^ (β ℓ i))).weightedOrder w =
      ((∑ i, a' i * β ℓ i : ℕ) : ℕ∞) := by
    intro ℓ
    rw [weightedOrder_algHom_shifted_monomial]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hp : p i = 0
    · rw [ite_eq_left hp, hfin, nsmul_eq_mul, mul_comm]
      simp [ha', hp]
    · rw [ite_eq_right hp, smul_zero]
      simp [ha', hp]
  have hA := sum_weightedOrder_le_logDiscrepancy ψ w
  simp only [hfin] at hA
  have ha'le : ∑ i, (a' i : ℕ∞) ≤ ∑ i, (a i : ℕ∞) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hp : p i = 0
    · simp [ha', hp]
    · simp [ha', hp]
  have hwpos : 1 ≤ ∑ j, w j := by
    by_contra h0
    push Not at h0
    apply hw
    funext j
    have : w j ≤ ∑ j, w j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.zero_apply]
    omega
  by_cases ha0 : a' = 0
  · obtain ⟨ℓ⟩ := ‹Nonempty ι›
    refine ⟨ℓ, ?_⟩
    rw [hval]
    simp only [ha0, Pi.zero_apply, zero_mul, Finset.sum_const_zero, Nat.cast_zero]
    have h1 : ((1 : ℕ) : ℕ∞) ≤ (h : ℕ∞) * ((∑ j, w j : ℕ) : ℕ∞) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc (0 : ℕ∞) < 1 := by norm_num
      _ ≤ (h : ℕ∞) * ((∑ j, w j : ℕ) : ℕ∞) := by exact_mod_cast h1
      _ ≤ _ := by gcongr; exact le_self_add
  · obtain ⟨ℓ, hℓ⟩ := hβ a' ha0
    refine ⟨ℓ, ?_⟩
    rw [hval]
    calc ((∑ i, a' i * β ℓ i : ℕ) : ℕ∞) < ((h * ∑ i, a' i : ℕ) : ℕ∞) := by exact_mod_cast hℓ
      _ = (h : ℕ∞) * ∑ i, (a' i : ℕ∞) := by push_cast; rfl
      _ ≤ (h : ℕ∞) * ∑ i, (a i : ℕ∞) := by gcongr
      _ ≤ _ := by gcongr

omit [DecidableEq K] [DecidableEq σ] in
/-- For generators g_ℓ containing the monomial x^β_ℓ, monomial valuations in the coordinates x
satisfy v_w(g_ℓ) ≤ ⟨w, β_ℓ⟩, so the strict inequality of (34) holds for the original ideal along
these valuations. -/
theorem exists_generator_weightedOrder_lt {ι : Type*} (g : ι → MvPowerSeries σ K)
    (β : ι → (σ →₀ ℕ)) (hg : ∀ ℓ, coeff (β ℓ) (g ℓ) ≠ 0) (h : ℕ) (w : σ → ℕ)
    (hβ : ∃ ℓ, Finsupp.weight w (β ℓ) < h * ∑ i, w i) :
    ∃ ℓ, (g ℓ).weightedOrder w < ((h * ∑ i, w i : ℕ) : ℕ∞) := by
  obtain ⟨ℓ, hℓ⟩ := hβ
  exact ⟨ℓ, lt_of_le_of_lt (weightedOrder_le w (hg ℓ)) (by exact_mod_cast hℓ)⟩

end MixedFujita
