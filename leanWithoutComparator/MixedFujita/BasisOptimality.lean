/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InitialExponents
public import MixedFujita.PerturbedValues
public import MixedFujita.FirstVariation
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Exponential optimality of an adapted initial-coefficient basis. An invertible
coefficient matrix has a nonzero permutation term. That permutation matches
every vector in any competing basis to a distinct coefficient position.
Coefficientwise bounds give the exponential-sum comparison directly, without
sorting a filtration or performing Gaussian elimination.
-/

@[expose] public section

namespace MixedFujita

theorem exists_nonzero_permutation_of_det_ne_zero {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (M : Matrix ι ι K) (hM : M.det ≠ 0) :
    ∃ π : Equiv.Perm ι, ∀ i, M (π i) i ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hM
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro π _
  obtain ⟨i, hi⟩ := h π
  rw [Finset.prod_eq_zero (f := fun k => M (π k) k) (Finset.mem_univ i) hi, smul_zero]

section AbstractCoefficientSystem

variable {K V α : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [LinearOrder α] [WellFoundedLT α]

theorem basis_coefficient_permutation (f : V →ₗ[K] (α → K)) (hf : Function.Injective f)
    (B : Module.Basis (initialIndexSet f) K V) :
    ∃ π : Equiv.Perm (initialIndexSet f), ∀ i, f (B i) (π i) ≠ 0 := by
  classical
  let := (initialIndexSet_finite f).fintype
  let M : Matrix (initialIndexSet f) (initialIndexSet f) K :=
    fun p q => initialCoefficientMap f (B q) p
  have hcols : LinearIndependent K M.col :=
    B.linearIndependent.map' (initialCoefficientMap f)
      ((LinearMap.ker_eq_bot).mpr (initialCoefficientMap_injective f hf))
  have hdet : M.det ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col hcols)
  exact exists_nonzero_permutation_of_det_ne_zero M hdet

theorem basis_initial_weight_sum_le (f : V →ₗ[K] (α → K)) (hf : Function.Injective f)
    [Fintype (initialIndexSet f)] (B : Module.Basis (initialIndexSet f) K V)
    (l : α → ℝ) (ν : V → ℝ) {j : ℝ} (hj : 0 < j)
    (hν : ∀ v p, f v p ≠ 0 → ν v ≤ l p) :
    (∑ p : initialIndexSet f, Real.exp (-l p / j)) ≤
      ∑ i : initialIndexSet f, Real.exp (-ν (B i) / j) := by
  classical
  obtain ⟨π, hπ⟩ := basis_coefficient_permutation f hf B
  rw [← Equiv.sum_comp π (fun p : initialIndexSet f => Real.exp (-l p / j))]
  apply Finset.sum_le_sum
  intro i _
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg (hν (B i) (π i) (hπ i))) hj.le

theorem initialCoefficientBasis_exponential_optimal
    (f : V →ₗ[K] (α → K)) (hf : Function.Injective f) [Fintype (initialIndexSet f)]
    (B : Module.Basis (initialIndexSet f) K V) (l : α → ℝ) (ν : V → ℝ)
    {j : ℝ} (hj : 0 < j)
    (hν : ∀ v p, f v p ≠ 0 → ν v ≤ l p)
    (hinit : ∀ p, ν (initialCoefficientBasis f hf p) = l p) :
    (∑ p : initialIndexSet f, Real.exp (-ν (initialCoefficientBasis f hf p) / j)) ≤
      ∑ i : initialIndexSet f, Real.exp (-ν (B i) / j) := by
  simpa only [hinit] using basis_initial_weight_sum_le f hf B l ν hj hν

end AbstractCoefficientSystem

variable {σ K : Type*} [Fintype σ] [Field K]

noncomputable def weightedSubspaceInitialBasis (m : MonomialOrder σ) (w : σ → ℝ)
    (v : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S] :
    Module.Basis (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) K S :=
  initialCoefficientBasis _ (subspaceCoefficientMap_injective _ _)

theorem weightedSubspaceInitialBasis_spec (m : MonomialOrder σ) (w : σ → ℝ)
    (v : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S]
    (p : initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) :
    IsInitialMonomial (weightedMonomialOrder m w v hw)
      (weightedSubspaceInitialBasis m w v hw S p).val
      ((weightedMonomialOrder m w v hw).toSyn.symm p.val) := by
  let n := weightedMonomialOrder m w v hw
  have h := initialCoefficientBasis_spec (subspaceCoefficientMap n S)
    (subspaceCoefficientMap_injective n S) p
  change IsInitialMonomial n
    (initialCoefficientBasis (subspaceCoefficientMap n S) (subspaceCoefficientMap_injective n S) p).val
    (n.toSyn.symm p.val)
  rw [initialMonomial_iff_initialCoefficient, n.toSyn.apply_symm_apply]
  exact h

theorem weightedSubspaceInitialBasis_value (m : MonomialOrder σ) (w : σ → ℝ)
    (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i) (S : Submodule K (MvPowerSeries σ K))
    [FiniteDimensional K S]
    (p : initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) :
    powerSeriesPerturbedValue m w v u hw (weightedSubspaceInitialBasis m w v hw S p).val 0 =
      realExponentWeight w ((weightedMonomialOrder m w v hw).toSyn.symm p.val) :=
  powerSeriesPerturbedValue_zero m w v u hw (weightedSubspaceInitialBasis_spec m w v hw S p)

/-- Actual power-series bases: the constructed adapted basis minimizes the old exponential sum. -/
theorem weightedSubspaceInitialBasis_exponential_optimal
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S]
    [Fintype (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S))]
    (B : Module.Basis (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) K S)
    {j : ℝ} (hj : 0 < j) :
    (∑ p, Real.exp (-powerSeriesPerturbedValue m w v u hw
      (weightedSubspaceInitialBasis m w v hw S p).val 0 / j)) ≤
      ∑ i, Real.exp (-powerSeriesPerturbedValue m w v u hw (B i).val 0 / j) := by
  let n := weightedMonomialOrder m w v hw
  apply initialCoefficientBasis_exponential_optimal
    (subspaceCoefficientMap n S) (subspaceCoefficientMap_injective n S) B
    (fun p => realExponentWeight w (n.toSyn.symm p))
    (fun φ => powerSeriesPerturbedValue m w v u hw φ.val 0) hj
  · intro φ p hp
    have hp' : MvPowerSeries.coeff (n.toSyn.symm p) φ.val ≠ 0 := hp
    exact powerSeriesPerturbedValue_le_weight_of_coeff m w v u hw hp'
  · exact weightedSubspaceInitialBasis_value m w v u hw S

theorem weightedSubspaceInitialBasis_objective_optimal
    (m : MonomialOrder σ) (w : σ → ℝ) (v u : σ → ℕ) (hw : ∀ i, 0 ≤ w i)
    (S : Submodule K (MvPowerSeries σ K)) [FiniteDimensional K S]
    [Fintype (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S))]
    (B : Module.Basis (initialIndexSet (subspaceCoefficientMap (weightedMonomialOrder m w v hw) S)) K S)
    (A : ℝ → ℝ) (t : ℝ) {j : ℝ} (hj : 0 < j) :
    sectionExponentialObjective Finset.univ t j A
      (fun p => powerSeriesPerturbedValue m w v u hw (weightedSubspaceInitialBasis m w v hw S p).val) 0 ≤
    sectionExponentialObjective Finset.univ t j A
      (fun i => powerSeriesPerturbedValue m w v u hw (B i).val) 0 := by
  rw [sectionExponentialObjective_factor, sectionExponentialObjective_factor]
  apply mul_le_mul_of_nonneg_left
    (weightedSubspaceInitialBasis_exponential_optimal m w v u hw S B hj)
  exact div_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _)

end MixedFujita
