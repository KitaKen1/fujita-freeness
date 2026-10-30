/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorJetCriterion
public import MixedFujita.ProjectiveChartAlgebra
public import MixedFujita.FormalCurveThreshold

/-!
Comparison of the global homogeneous jet equations with affine chart jets. Euler's identity
eliminates differentiation in the normalized coordinate. The resulting ideal equality is over
an arbitrary commutative coefficient ring; in characteristic zero it gives the exact chart
order condition, and on the projective line the original formal-test threshold condition.
-/

@[expose] public section

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Derivatives

variable {σ J R : Type*} [CommRing R]

/-- Differentiating an element of the h-jet ideal lands in the next jet ideal, including the
Leibniz terms coming from arbitrary polynomial coefficients. -/
theorem pderiv_mem_polynomialJetIdeal_succ (g : J → MvPolynomial σ R) (h : ℕ)
    (i : σ) {p : MvPolynomial σ R} (hp : p ∈ polynomialJetIdeal g h) :
    MvPolynomial.pderiv i p ∈ polynomialJetIdeal g (h + 1) := by
  change p ∈ Submodule.span (MvPolynomial σ R)
    {q | ∃ (j : J) (L : List σ), L.length < h ∧ q = polynomialIteratedPDeriv L (g j)} at hp
  refine Submodule.span_induction (fun q hq => ?_) ?_
    (fun p q _ _ hp hq => ?_) (fun a q hq ih => ?_) hp
  · obtain ⟨j, L, hL, rfl⟩ := hq
    exact Ideal.subset_span ⟨j, i :: L, by simpa using Nat.succ_lt_succ hL, rfl⟩
  · simpa only [map_zero] using (polynomialJetIdeal g (h + 1)).zero_mem
  · simpa only [map_add] using (polynomialJetIdeal g (h + 1)).add_mem hp hq
  · change MvPolynomial.pderiv i (a * q) ∈ polynomialJetIdeal g (h + 1)
    rw [MvPolynomial.pderiv_mul]
    exact (polynomialJetIdeal g (h + 1)).add_mem
      ((polynomialJetIdeal g (h + 1)).mul_mem_left _
        (polynomialJetIdeal_mono g (Nat.le_succ h) hq))
      ((polynomialJetIdeal g (h + 1)).mul_mem_left _ ih)

end Derivatives

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Free-coordinate differentiation commutes with dehomogenization. -/
theorem pderiv_projectiveDehomogenize (k : Fin n) (i : {j : Fin n // j ≠ k})
    (f : MvPolynomial (Fin n) R) :
    MvPolynomial.pderiv i (projectiveDehomogenize R k f) =
      projectiveDehomogenize R k (MvPolynomial.pderiv i.val f) := by
  classical
  have hX (j : Fin n) :
      MvPolynomial.pderiv i (projectiveDehomogenize R k (MvPolynomial.X j)) =
        projectiveDehomogenize R k (MvPolynomial.pderiv i.val (MvPolynomial.X j)) := by
    by_cases hjk : j = k
    · subst j
      simp [projectiveDehomogenize_X_self, MvPolynomial.pderiv_X_of_ne i.property.symm]
    · by_cases hji : j = i.val
      · subst j
        rw [projectiveDehomogenize_X_other R k i]
        simp
      · have hsub : (⟨j, hjk⟩ : {j : Fin n // j ≠ k}) ≠ i := by
          intro hh
          exact hji (congrArg Subtype.val hh)
        rw [projectiveDehomogenize_X_other R k ⟨j, hjk⟩]
        simp [MvPolynomial.pderiv_X_of_ne hsub, MvPolynomial.pderiv_X_of_ne hji]
  induction f using MvPolynomial.induction_on with
  | C r => simp [projectiveDehomogenize_C]
  | add f g ihf ihg => simp only [map_add, ihf, ihg]
  | mul_X f j ih =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add]
    rw [ih, hX]

/-- Euler's identity expresses the derivative in the normalized coordinate using the form
and its free-coordinate derivatives; there is no division by the homogeneous degree. -/
theorem projectiveDehomogenize_pderiv_self (k : Fin n) (f : MvPolynomial (Fin n) R)
    (d : ℕ) (hf : f.IsHomogeneous d) :
    projectiveDehomogenize R k (MvPolynomial.pderiv k f) =
      d • projectiveDehomogenize R k f - ∑ i : {j : Fin n // j ≠ k},
        MvPolynomial.X i * MvPolynomial.pderiv i (projectiveDehomogenize R k f) := by
  classical
  have he := congrArg (projectiveDehomogenize R k) hf.sum_X_mul_pderiv
  simp only [map_sum, map_mul, map_nsmul] at he
  have hs : ∑ j : Fin n, projectiveDehomogenize R k (MvPolynomial.X j) *
      projectiveDehomogenize R k (MvPolynomial.pderiv j f) =
      projectiveDehomogenize R k (MvPolynomial.pderiv k f) +
        ∑ i : {j : Fin n // j ≠ k}, MvPolynomial.X i *
          MvPolynomial.pderiv i (projectiveDehomogenize R k f) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k),
      projectiveDehomogenize_X_self, one_mul]
    congr 1
    rw [Finset.sum_subtype (p := fun j : Fin n => j ≠ k) (Finset.univ.erase k) (fun j => by simp)]
    apply Finset.sum_congr rfl
    intro j _
    rw [projectiveDehomogenize_X_other R k j, ← pderiv_projectiveDehomogenize k j]
  rw [hs] at he
  exact eq_sub_iff_add_eq.mpr he

/-- Every global iterated derivative dehomogenizes into the affine jet ideal of the same
cutoff. The normalized-coordinate case uses Euler's identity and derivative stability. -/
theorem projectiveDehomogenize_iterated_mem_jet {J : Type*} (k : Fin n)
    (g : J → MvPolynomial (Fin n) R) (d : J → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (j : J) (L : List (Fin n)) :
    projectiveDehomogenize R k (polynomialIteratedPDeriv L (g j)) ∈
      polynomialJetIdeal (fun j => projectiveDehomogenize R k (g j)) (L.length + 1) := by
  classical
  let g' := fun j => projectiveDehomogenize R k (g j)
  induction L with
  | nil => exact Ideal.subset_span ⟨j, [], by simp, rfl⟩
  | cons i L ih =>
    change projectiveDehomogenize R k (MvPolynomial.pderiv i
      (polynomialIteratedPDeriv L (g j))) ∈ polynomialJetIdeal g' (L.length + 1 + 1)
    by_cases hi : i = k
    · subst i
      rw [projectiveDehomogenize_pderiv_self k _ (d j - L.length)
        (polynomialIteratedPDeriv_isHomogeneous L (g j) (d j) (hg j))]
      apply (polynomialJetIdeal g' (L.length + 1 + 1)).sub_mem
      · have hq := polynomialJetIdeal_mono g' (Nat.le_succ (L.length + 1)) ih
        simpa only [nsmul_eq_mul] using
          (polynomialJetIdeal g' (L.length + 1 + 1)).mul_mem_left
            ((d j - L.length : ℕ) : MvPolynomial {i : Fin n // i ≠ k} R) hq
      · apply (polynomialJetIdeal g' (L.length + 1 + 1)).sum_mem
        intro i _
        exact (polynomialJetIdeal g' (L.length + 1 + 1)).mul_mem_left _
          (pderiv_mem_polynomialJetIdeal_succ g' (L.length + 1) i ih)
    · rw [← pderiv_projectiveDehomogenize k ⟨i, hi⟩]
      exact pderiv_mem_polynomialJetIdeal_succ g' (L.length + 1) ⟨i, hi⟩ ih

/-- Iterated free-coordinate derivatives are restrictions of the corresponding global words. -/
theorem polynomialIteratedPDeriv_projectiveDehomogenize (k : Fin n)
    (L : List {i : Fin n // i ≠ k}) (f : MvPolynomial (Fin n) R) :
    polynomialIteratedPDeriv L (projectiveDehomogenize R k f) =
      projectiveDehomogenize R k (polynomialIteratedPDeriv (L.map Subtype.val) f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [polynomialIteratedPDeriv, ih, pderiv_projectiveDehomogenize]
    rfl

/-- The actual global homogeneous jet ideal restricts to exactly the affine chart jet ideal.
This proves the compatibility of the chart equations, without a supplied overlap hypothesis. -/
theorem polynomialJetIdeal_projectiveDehomogenize {J : Type*} (k : Fin n)
    (g : J → MvPolynomial (Fin n) R) (d : J → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (h : ℕ) :
    Ideal.map (projectiveDehomogenize R k) (polynomialJetIdeal g h) =
      polynomialJetIdeal (fun j => projectiveDehomogenize R k (g j)) h := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, polynomialJetIdeal_le_iff]
    intro j L hL
    exact polynomialJetIdeal_mono _ (by omega)
      (projectiveDehomogenize_iterated_mem_jet k g d hg j L)
  · rw [polynomialJetIdeal_le_iff]
    intro j L hL
    rw [polynomialIteratedPDeriv_projectiveDehomogenize]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span
      ⟨j, L.map Subtype.val, by simpa only [List.length_map] using hL, rfl⟩)

section Taylor

variable {K : Type*} [Field K]

/-- Dehomogenization followed by affine Taylor translation is the original shifted chart form. -/
theorem affinePolynomialTaylor_projectiveDehomogenize (k : Fin n)
    (p : {i : Fin n // i ≠ k} → K) (f : MvPolynomial (Fin n) K) :
    affinePolynomialTaylor p (projectiveDehomogenize K k f) = chartShiftedForm k p f := by
  classical
  have heq : (affinePolynomialTaylor p).toRingHom.comp (projectiveDehomogenize K k) =
      (MvPolynomial.aeval (fun i : Fin n =>
        if h : i = k then (1 : MvPowerSeries {i : Fin n // i ≠ k} K) else
          MvPowerSeries.C (p ⟨i, h⟩) + MvPowerSeries.X ⟨i, h⟩)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [affinePolynomialTaylor, projectiveDehomogenize, RingHom.comp_apply]
    · intro i
      by_cases hi : i = k <;>
        simp [affinePolynomialTaylor, projectiveDehomogenize, projectiveChartVariable,
          RingHom.comp_apply, hi]
  exact congrArg (fun H => H f) heq

/-- In characteristic zero the global jet equations in a chart are exactly the simultaneous
ordinary vanishing-order conditions, including zero forms and threshold equality. -/
theorem polynomialJetIdeal_chart_order_iff [CharZero K] {J : Type*}
    (k : Fin n) (g : J → MvPolynomial (Fin n) K) (d : J → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (h : ℕ)
    (p : {i : Fin n // i ≠ k} → K) :
    Ideal.map (projectiveDehomogenize K k) (polynomialJetIdeal g h) ≤
        RingHom.ker (MvPolynomial.eval p) ↔
      ∀ j, (h : ℕ∞) ≤ (chartShiftedForm k p (g j)).order := by
  rw [polynomialJetIdeal_projectiveDehomogenize k g d hg,
    polynomialJetIdeal_le_eval_ker_iff]
  simp only [affinePolynomialTaylor_projectiveDehomogenize]

/-- On a projective-line chart, the global jet equations detect precisely failure of the
original full formal-test threshold condition. -/
theorem polynomialJetIdeal_binary_chart_bad_iff [CharZero K] {J : Type*}
    (k : Fin 2) (g : J → MvPolynomial (Fin 2) K) (d : J → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (h : ℕ)
    (p : {i : Fin 2 // i ≠ k} → K) :
    Ideal.map (projectiveDehomogenize K k) (polynomialJetIdeal g h) ≤
        RingHom.ker (MvPolynomial.eval p) ↔
      ¬FormalSeriesThresholdCondition (fun j => chartShiftedForm k p (g j)) h := by
  have hcard : Fintype.card {i : Fin 2 // i ≠ k} = 1 := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [polynomialJetIdeal_chart_order_iff k g d hg h,
    formalSeriesThresholdCondition_iff_exists_order_lt hcard]
  simp only [not_exists, not_lt]

/-- For homogeneous binary forms, the original all-chart, all-point formal threshold condition
is avoidance of the chart restrictions of one global homogeneous jet ideal. -/
theorem projectiveThresholdCondition_binary_jet_criterion [CharZero K] [DecidableEq K]
    {J : Type*} (g : J → MvPolynomial (Fin 2) K) (d : J → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (h : ℕ) :
    ProjectiveThresholdCondition g h ↔ ∀ (k : Fin 2)
      (p : {i : Fin 2 // i ≠ k} → K),
      ¬Ideal.map (projectiveDehomogenize K k) (polynomialJetIdeal g h) ≤
        RingHom.ker (MvPolynomial.eval p) := by
  change (∀ (k : Fin 2) (p : {i : Fin 2 // i ≠ k} → K),
    FormalSeriesThresholdCondition (fun j => chartShiftedForm k p (g j)) h) ↔ _
  exact forall_congr' fun k => forall_congr' fun p => by
    simpa only [not_not] using
      (not_congr (polynomialJetIdeal_binary_chart_bad_iff k g d hg h p)).symm

end Taylor

end MixedFujita
