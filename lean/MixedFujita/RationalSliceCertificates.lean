/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConvexCertificates
public import MixedFujita.RationalSectionProducts
public import MixedFujita.SharedRationalProducts

/-!
Rational barycentric witnesses and explicit targets on a fixed-sum slice.
The targets c + delta*(e_a-e_b) give the strict weighted inequalities needed
in every projective chart, directly. No rational-polytope enumeration is
required. Threshold theory and geometric section multiplication remain open.
-/

@[expose] public section

namespace MixedFujita

open Filter Topology

theorem simplexVertexMatrix_rat_cast {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) :
    (simplexVertexMatrix v).map (fun q => (q : ℝ)) =
      simplexVertexMatrix (fun j i => (v j i : ℝ)) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [simplexVertexMatrix, Matrix.map]

theorem simplexVertexMatrix_det_rat_cast {n : ℕ} (v : Fin (n + 1) → Fin n → ℚ) :
    ((simplexVertexMatrix v).det : ℝ) =
      (simplexVertexMatrix (fun j i => (v j i : ℝ))).det := by
  rw [Rat.cast_det, simplexVertexMatrix_rat_cast]

theorem simplexWeights_rat_cast {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℚ) (x : Fin n → ℚ)
    (hv : (simplexVertexMatrix (fun j i => (v j i : ℝ))).det ≠ 0) :
    (fun j => (simplexWeights (K := ℚ) v x j : ℝ)) =
      simplexWeights (fun j i => (v j i : ℝ)) (fun i => (x i : ℝ)) := by
  have hq : (simplexVertexMatrix v).det ≠ 0 := by
    intro hzero
    apply hv
    rw [← simplexVertexMatrix_det_rat_cast, hzero, Rat.cast_zero]
  apply Eq.symm
  apply simplexWeights_eq_of_certificate _ _ (isUnit_iff_ne_zero.mpr hv)
  have h := simplexWeights_equation v x (isUnit_iff_ne_zero.mpr hq)
  have hcast := congrArg (fun y : Fin (n + 1) → ℚ => fun i => (y i : ℝ)) h
  rw [← simplexVertexMatrix_rat_cast]
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simpa [Matrix.map, Matrix.mulVec, dotProduct, simplexVertexMatrix] using congrFun hcast 0
  · simpa [Matrix.map, Matrix.mulVec, dotProduct, simplexVertexMatrix] using congrFun hcast k.succ

theorem exists_rational_simplex_combination {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℚ) (x : Fin n → ℚ)
    (hv : (simplexVertexMatrix (fun j i => (v j i : ℝ))).det ≠ 0)
    (hw : ∀ j, 0 < simplexWeights (fun j i => (v j i : ℝ)) (fun i => (x i : ℝ)) j) :
    ∃ q : Fin (n + 1) → ℚ≥0, (∑ j, q j) = 1 ∧
      (∀ j, 0 < (q j : ℚ)) ∧ ∑ j, (q j : ℚ) • v j = x := by
  have hq : (simplexVertexMatrix v).det ≠ 0 := by
    intro hzero
    apply hv
    rw [← simplexVertexMatrix_det_rat_cast, hzero, Rat.cast_zero]
  have hp (j) : 0 < simplexWeights v x j := by
    have hj := hw j
    rw [← simplexWeights_rat_cast v x hv] at hj
    change (0 : ℝ) < (simplexWeights (K := ℚ) v x j : ℝ) at hj
    exact_mod_cast hj
  let q : Fin (n + 1) → ℚ≥0 := fun j => ⟨simplexWeights v x j, (hp j).le⟩
  refine ⟨q, ?_, hp, ?_⟩
  · apply NNRat.coe_injective
    change NNRat.coeHom (∑ j, q j) = NNRat.coeHom 1
    rw [map_sum]
    change (∑ j, simplexWeights v x j) = 1
    exact simplexWeights_sum v x (isUnit_iff_ne_zero.mpr hq)
  · exact simplexWeights_combination v x (isUnit_iff_ne_zero.mpr hq)

def rationalSliceTarget {n : ℕ} (c : Fin n → ℚ) (δ : ℚ) (a b : Fin n) : Fin n → ℚ :=
  fun i => c i + δ * ((if i = a then 1 else 0) - (if i = b then 1 else 0))

theorem rationalSliceTarget_sum {n : ℕ} (c : Fin n → ℚ) (δ : ℚ) (a b : Fin n) :
    (∑ i, rationalSliceTarget c δ a b i) = ∑ i, c i := by
  simp only [rationalSliceTarget, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib]
  simp

theorem rationalSliceTarget_coordinate_bound {n : ℕ} (c : Fin n → ℚ) {δ : ℚ}
    (hδ : 0 ≤ δ) (a b i : Fin n) :
    |(rationalSliceTarget c δ a b i : ℝ) - (c i : ℝ)| ≤ (δ : ℝ) := by
  have h : |rationalSliceTarget c δ a b i - c i| ≤ δ := by
    unfold rationalSliceTarget
    split_ifs <;> simp [abs_of_nonneg hδ, hδ]
  exact_mod_cast h

theorem rationalSliceTarget_weight {n : ℕ} (c : Fin n → ℚ) (δ : ℚ)
    (a b : Fin n) (w : Fin n → ℝ) :
    (∑ i, w i * (rationalSliceTarget c δ a b i : ℝ)) =
      (∑ i, w i * (c i : ℝ)) + (δ : ℝ) * (w a - w b) := by
  have hcoord (i : Fin n) : (rationalSliceTarget c δ a b i : ℝ) =
      (c i : ℝ) + (δ : ℝ) *
        ((if i = a then (1 : ℝ) else 0) - (if i = b then (1 : ℝ) else 0)) := by
    unfold rationalSliceTarget
    split_ifs <;> push_cast <;> ring
  simp_rw [hcoord, mul_add, mul_sub, ← mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  simp
  ring

theorem rationalSliceTarget_strict_chart_weight {n : ℕ} (c : Fin n → ℚ) {δ : ℚ}
    (hδ : 0 < δ) (w : Fin n → ℝ) (k : Fin n)
    (hw : ∀ i, 0 ≤ w i) (hk : w k = 0) (hne : w ≠ 0) :
    ∃ a b : Fin n, (∑ i, w i * (rationalSliceTarget c δ a b i : ℝ)) <
      ∑ i, w i * (c i : ℝ) := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra h
    apply hne
    funext i
    exact not_exists.mp h i |> not_ne_iff.mp
  obtain ⟨i, hi⟩ := hex
  refine ⟨k, i, ?_⟩
  rw [rationalSliceTarget_weight, hk]
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ
  have hi' : 0 < w i := lt_of_le_of_ne (hw i) (Ne.symm hi)
  nlinarith

/-- All explicit fixed-sum targets admit positive rational combinations of
the same original rational vertices, for one positive rational delta. -/
theorem exists_rational_slice_combinations {n : ℕ}
    (v : Fin (n + 1) → Fin n → ℚ) (c : Fin n → ℚ)
    (hv : (simplexVertexMatrix (fun j i => (v j i : ℝ))).det ≠ 0)
    (hw : ∀ j, 0 < simplexWeights (fun j i => (v j i : ℝ)) (fun i => (c i : ℝ)) j) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ a b : Fin n,
      ∃ q : Fin (n + 1) → ℚ≥0, (∑ j, q j) = 1 ∧
        (∀ j, 0 < (q j : ℚ)) ∧ ∑ j, (q j : ℚ) • v j = rationalSliceTarget c δ a b := by
  have hpos : ∀ᶠ x in 𝓝 (fun i => (c i : ℝ)), ∀ j,
      0 < simplexWeights (fun j i => (v j i : ℝ)) x j := by
    apply Filter.eventually_all.mpr
    intro j
    have hj : ContinuousAt
        (fun x => simplexWeights (fun j i => (v j i : ℝ)) x j) (fun i => (c i : ℝ)) :=
      ((continuous_apply j).comp (continuous_simplexWeights_point _)).continuousAt
    exact hj.eventually (lt_mem_nhds (hw j))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpos
  obtain ⟨δ, hδ, hδr⟩ := exists_rat_btwn hr
  have hδq : (0 : ℚ) < δ := by exact_mod_cast hδ
  refine ⟨δ, hδq, ?_⟩
  intro a b
  apply exists_rational_simplex_combination v (rationalSliceTarget c δ a b) hv
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr]
  intro i
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact (rationalSliceTarget_coordinate_bound c hδq.le a b i).trans_lt hδr

/-- The equality-case lattice hypotheses now supply actual same-degree
vertices and positive rational witnesses for every explicit slice target. -/
theorem equality_mean_eventually_rational_slice_witnesses {n : ℕ}
    (E : ℕ → Finset (Fin n → ℕ)) (m : ℕ → ℕ) (c : Fin n → ℚ)
    {C : ℝ} (hm : Tendsto m atTop atTop) (hC : 0 < C)
    (hc : (fun i => (c i : ℝ)) ∈ positiveSimplexInterior C)
    (hcard : Tendsto (fun k => normalizedLatticeCard (E k) (m k)) atTop
      (𝓝 (C ^ n / (n.factorial : ℝ))))
    (hmean : Tendsto (fun k => normalizedLatticeMean (E k) (m k)) atTop
      (𝓝 ((n : ℝ) / (n + 1 : ℝ) * C))) :
    ∀ᶠ k in atTop, ∃ g : Fin (n + 1) → Fin n → ℕ,
      (∀ j, g j ∈ E k) ∧ ∃ δ : ℚ, 0 < δ ∧
      ∃ q : Fin n → Fin n → Fin (n + 1) → ℚ≥0,
        (∀ a b, (∑ j, q a b j) = 1) ∧
        (∀ a b j, 0 < (q a b j : ℚ)) ∧
        ∀ a b, (∑ j, (q a b j : ℚ) • (fun i => (g j i : ℚ) / m k)) =
          rationalSliceTarget c δ a b := by
  filter_upwards [equality_mean_eventually_surrounds_point E m (fun i => (c i : ℝ))
    hm hC hc hcard hmean] with k hk
  obtain ⟨g, hg, hd, hp, _⟩ := hk
  let v : Fin (n + 1) → Fin n → ℚ := fun j i => (g j i : ℚ) / m k
  have hcast : (fun j i => (v j i : ℝ)) = fun j i => (g j i : ℝ) / m k := by
    funext j i
    simp [v]
  have hdv : (simplexVertexMatrix (fun j i => (v j i : ℝ))).det ≠ 0 := by
    rwa [hcast]
  have hpv : ∀ j, 0 < simplexWeights (fun j i => (v j i : ℝ)) (fun i => (c i : ℝ)) j := by
    rwa [hcast]
  obtain ⟨δ, hδ, hq⟩ := exists_rational_slice_combinations v c hdv hpv
  choose q hsum hpos hcomb using hq
  exact ⟨g, hg, δ, hδ, q, hsum, hpos, hcomb⟩

/-- Realize the slice by actual power-series products with one common total
multiplicity. The normalized initial exponent is exactly each rational target. -/
theorem exists_shared_powerSeries_slice_products {n : ℕ} {K : Type*} [Field K]
    (order : MonomialOrder (Fin n)) (p : Fin (n + 1) → Fin n →₀ ℕ)
    (φ : Fin (n + 1) → MvPowerSeries (Fin n) K)
    (hφ : ∀ j, IsInitialMonomial order (φ j) (p j))
    (c : Fin n → ℚ) {m : ℕ} (hm : 0 < m)
    (hv : (simplexVertexMatrix (fun j i => (p j i : ℝ) / m)).det ≠ 0)
    (hw : ∀ j, 0 < simplexWeights (fun j i => (p j i : ℝ) / m)
      (fun i => (c i : ℝ)) j) :
    ∃ δ : ℚ, 0 < δ ∧ ∃ D : ℕ, 0 < D ∧
      ∃ k : (Fin n × Fin n) → Fin (n + 1) → ℕ,
        (∀ l, (∑ j, k l j) = D) ∧
        (∀ l, IsInitialMonomial order (∏ j, (φ j) ^ k l j) (∑ j, k l j • p j)) ∧
        (∀ l, (∏ j, (φ j) ^ k l j) ≠ 0) ∧
        ∀ l i, ((∑ j, k l j • p j) i : ℚ) / ((D : ℚ) * m) =
          rationalSliceTarget c δ l.1 l.2 i := by
  let v : Fin (n + 1) → Fin n → ℚ := fun j i => (p j i : ℚ) / m
  have hcast : (fun j i => (v j i : ℝ)) = fun j i => (p j i : ℝ) / m := by
    funext j i
    simp [v]
  have hv' : (simplexVertexMatrix (fun j i => (v j i : ℝ))).det ≠ 0 := by rwa [hcast]
  have hw' : ∀ j, 0 < simplexWeights (fun j i => (v j i : ℝ)) (fun i => (c i : ℝ)) j := by
    rwa [hcast]
  obtain ⟨δ, hδ, hq⟩ := exists_rational_slice_combinations v c hv' hw'
  choose q hsum _hpos hcomb using hq
  let Q : (Fin n × Fin n) → Fin (n + 1) → ℚ≥0 := fun l => q l.1 l.2
  let D := sharedRationalDenominator Finset.univ Q
  let k := sharedRationalMultiplicity Finset.univ Q
  refine ⟨δ, hδ, D, sharedRationalDenominator_pos _ _, k, ?_, ?_, ?_, ?_⟩
  · intro l
    exact sharedRationalMultiplicity_sum Finset.univ Q l (hsum l.1 l.2)
  · intro l
    exact sharedRational_product_initialMonomial order Finset.univ Q φ p (fun j _ => hφ j) l
  · intro l
    exact sharedRational_product_ne_zero order Finset.univ Q φ p (fun j _ => hφ j) l
  · intro l i
    exact sharedRational_normalized_exponent Finset.univ Q p
      (fun l => rationalSliceTarget c δ l.1 l.2) hm (fun l => hcomb l.1 l.2) l i

end MixedFujita
