/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialUniversalRegularity
public import MixedFujita.ProjectiveUniversalNonzeroCharts
public import MixedFujita.RegularPrincipalIdeal

/-!
On each standard projective chart the homogeneous nonzero locus is covered
by finitely many coefficient basic opens. On those opens, after arbitrary
coefficient-ring base change, the actual equation is regular and its
principal ideal is linearly equivalent to the chart ring. The relative
Cartier scheme construction, quotient flatness and lct remain separate.
-/

@[expose] public section

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem projectiveHomogeneous_chart_coefficient_cover (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    (polynomialNonzeroLocus f : Set (PrimeSpectrum R)) =
      ⋃ q ∈ (projectiveDehomogenize R k f).support,
        (PrimeSpectrum.basicOpen ((projectiveDehomogenize R k f).coeff q) :
          Set (PrimeSpectrum R)) := by
  rw [← projectiveHomogeneous_nonzeroLocus_chart k d f hf]
  exact polynomialNonzeroLocus_finite_basicOpen_cover _

theorem projectiveChart_unit_coefficient_universal_regular (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S) :
    projectiveDehomogenize S k (MvPolynomial.map c f) ∈
      nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} S) := by
  rw [← projectiveDehomogenize_scalar_commutes]
  exact finitePolynomial_unit_coefficient_baseChange c _ q hq

theorem projectiveChart_localized_coefficient_universal_regular (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    [Algebra R S] [IsLocalization.Away ((projectiveDehomogenize R k f).coeff q) S]
    (c : S →+* T) :
    projectiveDehomogenize T k (MvPolynomial.map (c.comp (algebraMap R S)) f) ∈
      nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} T) := by
  rw [← projectiveDehomogenize_scalar_commutes]
  exact finitePolynomial_localized_coefficient_universal_regular _ q c

theorem projectiveHomogeneous_chart_universal_regular_cover (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (p : PrimeSpectrum R)
    (hp : p ∈ polynomialNonzeroLocus f) :
    ∃ q ∈ (projectiveDehomogenize R k f).support,
      (projectiveDehomogenize R k f).coeff q ∉ p.asIdeal ∧
        ∀ c : Localization.Away ((projectiveDehomogenize R k f).coeff q) →+* S,
          projectiveDehomogenize S k
            (MvPolynomial.map (c.comp (algebraMap R
              (Localization.Away ((projectiveDehomogenize R k f).coeff q)))) f) ∈
                nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} S) := by
  rw [← projectiveHomogeneous_nonzeroLocus_chart k d f hf] at hp
  obtain ⟨q, hq, hpq⟩ := polynomialNonzeroLocus_local_coefficient _ p hp
  exact ⟨q, hq, hpq, fun c => projectiveChart_localized_coefficient_universal_regular k f q c⟩

noncomputable def projectiveChartRegularIdealEquiv (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S) :
    MvPolynomial {j : Fin n // j ≠ k} S ≃ₗ[MvPolynomial {j : Fin n // j ≠ k} S]
      Ideal.span {projectiveDehomogenize S k (MvPolynomial.map c f)} :=
  regularPrincipalIdealEquiv _ (projectiveChart_unit_coefficient_universal_regular k f q hq c)

theorem projectiveChartRegularIdealEquiv_apply (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S)
    (g : MvPolynomial {j : Fin n // j ≠ k} S) :
    (projectiveChartRegularIdealEquiv k f q hq c g : MvPolynomial {j : Fin n // j ≠ k} S) =
      projectiveDehomogenize S k (MvPolynomial.map c f) * g := rfl

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousChartFraction_regular_of_affine (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d)
    (hreg : projectiveDehomogenize R k f ∈
      nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} R)) :
    HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.isHomogeneous_X R k) d f (by simpa using hf) ∈
        nonZeroDivisors (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)) := by
  apply mem_nonZeroDivisors_of_injective (projectiveChartRingEquiv R k).injective
  change projectiveChartLocalizationToAffine R k _ ∈ _
  rw [projectiveChartLocalizationToAffine_mk R k d f hf]
  exact hreg

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousChartFraction_unit_coefficient_baseChange (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d)
    (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S) :
    HomogeneousLocalization.Away.mk (MvPolynomial.homogeneousSubmodule (Fin n) S)
      (MvPolynomial.isHomogeneous_X S k) d (MvPolynomial.map c f)
      (by simpa using hf.map c) ∈
        nonZeroDivisors (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)) :=
  homogeneousChartFraction_regular_of_affine k d _ (hf.map c)
    (projectiveChart_unit_coefficient_universal_regular k f q hq c)

end MixedFujita
