/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HomogeneousTaylor

/-!
An explicit linear combination with nonzero degree-d Taylor form has exact
order d, provided all summands have order at least d. Extraction is an actual
linear map and commutes with the same scalar coefficients. These are power
series and module results; a geometric Taylor map from ordinary sections is
still an input, not constructed by this module.
-/

@[expose] public section

namespace MixedFujita

variable {σ K ι V : Type*} [Finite σ] [Field K] [AddCommGroup V] [Module K V]

noncomputable def taylorLeadingLinearMap (d : ℕ) (T : V →ₗ[K] MvPowerSeries σ K) :
    V →ₗ[K] MvPolynomial σ K := (homogeneousTaylorForm d).comp T

theorem homogeneousTaylorForm_linearCombination (d : ℕ) (I : Finset ι)
    (φ : ι → MvPowerSeries σ K) (a : ι → K) :
    homogeneousTaylorForm d (∑ l ∈ I, a l • φ l) =
      ∑ l ∈ I, MvPolynomial.C (a l) * homogeneousTaylorForm d (φ l) := by
  simp only [map_sum, map_smul, MvPolynomial.smul_eq_C_mul]

theorem taylorLeadingLinearMap_linearCombination (d : ℕ)
    (T : V →ₗ[K] MvPowerSeries σ K) (I : Finset ι) (s : ι → V) (a : ι → K) :
    taylorLeadingLinearMap d T (∑ l ∈ I, a l • s l) =
      ∑ l ∈ I, MvPolynomial.C (a l) * taylorLeadingLinearMap d T (s l) := by
  simp only [map_sum, map_smul, MvPolynomial.smul_eq_C_mul]

omit [Finite σ] in
theorem powerSeries_linearCombination_order_ge (d : ℕ) (I : Finset ι)
    (φ : ι → MvPowerSeries σ K) (a : ι → K)
    (hφ : ∀ l ∈ I, (d : ℕ∞) ≤ (φ l).order) :
    (d : ℕ∞) ≤ (∑ l ∈ I, a l • φ l).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro p hp
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro l hl
  rw [MvPowerSeries.coeff_of_lt_order
    (lt_of_lt_of_le (by exact_mod_cast hp) (hφ l hl)), mul_zero]

theorem homogeneousTaylorForm_nonzero_iff_order (d : ℕ) (φ : MvPowerSeries σ K)
    (hφ : (d : ℕ∞) ≤ φ.order) :
    homogeneousTaylorForm d φ ≠ 0 ↔ φ.order = (d : ℕ∞) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := MvPolynomial.exists_coeff_ne_zero h
    have hd : p.degree = d := by
      by_contra hn
      exact hp (by simp [homogeneousTaylorForm_coeff, hn])
    have hcoeff : MvPowerSeries.coeff p φ ≠ 0 := by
      simpa only [homogeneousTaylorForm_coeff, hd, ite_true] using hp
    exact le_antisymm (hd ▸ MvPowerSeries.order_le hcoeff) hφ
  · intro h
    obtain ⟨⟨p, hp, hd⟩, _⟩ := MvPowerSeries.order_eq_nat.mp h
    simpa only [hd] using homogeneousTaylorForm_nonzero φ p hp

theorem powerSeries_linearCombination_exact_order (d : ℕ) (I : Finset ι)
    (φ : ι → MvPowerSeries σ K) (a : ι → K)
    (hφ : ∀ l ∈ I, (d : ℕ∞) ≤ (φ l).order)
    (hform : (∑ l ∈ I, MvPolynomial.C (a l) * homogeneousTaylorForm d (φ l)) ≠ 0) :
    (∑ l ∈ I, a l • φ l).order = (d : ℕ∞) := by
  apply (homogeneousTaylorForm_nonzero_iff_order d _
    (powerSeries_linearCombination_order_ge d I φ a hφ)).mp
  rwa [homogeneousTaylorForm_linearCombination]

theorem taylor_linearCombination_exact_order (d : ℕ)
    (T : V →ₗ[K] MvPowerSeries σ K) (I : Finset ι) (s : ι → V) (a : ι → K)
    (hs : ∀ l ∈ I, (d : ℕ∞) ≤ (T (s l)).order)
    (hform : (∑ l ∈ I, MvPolynomial.C (a l) * taylorLeadingLinearMap d T (s l)) ≠ 0) :
    (T (∑ l ∈ I, a l • s l)).order = (d : ℕ∞) ∧
      (∑ l ∈ I, a l • s l) ≠ 0 := by
  have horder : (T (∑ l ∈ I, a l • s l)).order = (d : ℕ∞) := by
    simp only [map_sum, map_smul]
    exact powerSeries_linearCombination_exact_order d I (fun l => T (s l)) a hs hform
  refine ⟨horder, ?_⟩
  intro h0
  rw [h0, map_zero, MvPowerSeries.order_zero] at horder
  exact (ENat.natCast_ne_top d) horder.symm

theorem taylor_linearCombination_mem_span (I : Finset ι) (s : ι → V) (a : ι → K) :
    ∑ l ∈ I, a l • s l ∈ Submodule.span K (Set.range (fun l : I => s l)) := by
  classical
  apply Submodule.sum_mem
  intro l hl
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)

theorem homogeneousTaylorForm_remainder_order (d : ℕ) (φ : MvPowerSeries σ K)
    (hφ : (d : ℕ∞) ≤ φ.order) :
    ((d + 1 : ℕ) : ℕ∞) ≤
      (φ - (homogeneousTaylorForm d φ : MvPowerSeries σ K)).order := by
  apply MvPowerSeries.nat_le_order
  intro p hp
  rw [map_sub, MvPolynomial.coeff_coe, homogeneousTaylorForm_coeff]
  by_cases hd : p.degree = d
  · simp [hd]
  · have hlt : p.degree < d := by omega
    rw [ite_eq_right hd, sub_zero]
    exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt) hφ)

end MixedFujita
