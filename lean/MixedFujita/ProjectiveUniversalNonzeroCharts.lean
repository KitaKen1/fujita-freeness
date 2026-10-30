/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.UniversalHomogeneousForm
public import MixedFujita.ProjectiveChartEquiv

/-!
A homogeneous form is zero on a standard chart exactly when the form is
zero. Over its nonzero parameter locus every chart residue-field equation
is a nonzerodivisor. This proves the local fiberwise regularity input; the
relative effective Cartier criterion and lct comparison remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type*} [CommRing R]

theorem homogeneousChartFraction_eq_zero_iff (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.isHomogeneous_X R k) d f
      (by simpa using hf) = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hv := congrArg HomogeneousLocalization.val h
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk'] at hv
    obtain ⟨s, hs⟩ := (IsLocalization.mk'_eq_zero_iff f _).mp hv
    obtain ⟨j, hj⟩ := s.property
    have hm : (MvPolynomial.X k : MvPolynomial (Fin n) R) ^ j * f = 0 := by
      simpa only [hj] using hs
    exact (MvPolynomial.isRegular_X_pow (R := R) (n := k) j).left
      (by simpa only [mul_zero] using hm)
  · intro h
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero, h]
    exact Localization.mk_zero _

theorem projectiveDehomogenize_eq_zero_iff (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    projectiveDehomogenize R k f = 0 ↔ f = 0 := by
  constructor
  · intro h
    let z := HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.isHomogeneous_X R k) d f
      (by simpa using hf)
    have hz : z = 0 := by
      apply (show Function.Injective (projectiveChartLocalizationToAffine R k) from
        (projectiveChartRingEquiv R k).injective)
      rw [map_zero]
      exact (projectiveChartLocalizationToAffine_mk R k d f hf).trans h
    exact (homogeneousChartFraction_eq_zero_iff k d f hf).mp hz
  · intro h
    rw [h, map_zero]

theorem projectiveHomogeneous_nonzeroLocus_chart (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    polynomialNonzeroLocus (projectiveDehomogenize R k f) = polynomialNonzeroLocus f := by
  apply TopologicalSpace.Opens.ext
  ext p
  change p ∈ polynomialNonzeroLocus (projectiveDehomogenize R k f) ↔
    p ∈ polynomialNonzeroLocus f
  rw [polynomialNonzeroLocus_mem, polynomialNonzeroLocus_mem,
    projectiveDehomogenize_scalar_commutes]
  exact not_congr (projectiveDehomogenize_eq_zero_iff k d _
    (hf.map (algebraMap R p.asIdeal.ResidueField)))

theorem projectiveHomogeneous_fiber_chart_regular (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (p : PrimeSpectrum R) :
    p ∈ polynomialNonzeroLocus f ↔
      projectiveDehomogenize p.asIdeal.ResidueField k
        (MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) f) ∈
          nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} p.asIdeal.ResidueField) := by
  rw [← projectiveHomogeneous_nonzeroLocus_chart k d f hf,
    polynomialNonzeroLocus_fiber_regular, projectiveDehomogenize_scalar_commutes]

theorem universalParameterHomogeneousForm_chart_regular {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (q : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d)
    (p : PrimeSpectrum (MvPolynomial ι (Polynomial K))) (hp : p ∈
      polynomialNonzeroLocus (universalParameterHomogeneousForm I w q f)) (k : Fin n) :
    projectiveDehomogenize p.asIdeal.ResidueField k
      (MvPolynomial.map (algebraMap (MvPolynomial ι (Polynomial K)) p.asIdeal.ResidueField)
        (universalParameterHomogeneousForm I w q f)) ∈
      nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} p.asIdeal.ResidueField) :=
  (projectiveHomogeneous_fiber_chart_regular k d _
    (universalParameterHomogeneousForm_isHomogeneous I w q f d hf) p).mp hp

end MixedFujita
