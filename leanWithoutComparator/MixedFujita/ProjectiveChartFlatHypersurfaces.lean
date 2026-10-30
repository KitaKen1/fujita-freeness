/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineHypersurfaceGeometry
public import MixedFujita.ProjectiveUniversalRegularity

/-!
The coefficient-open cover on every projective chart now has flat actual
affine hypersurfaces of local finite presentation, cut out by regular
equations. Their inclusions are actual closed immersions. Flatness persists
after arbitrary coefficient-ring maps. Global projective relative Cartier
gluing and lct remain separate.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry

variable {n : ℕ} {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem projectiveChart_unit_coefficient_quotient_flat (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S) :
    Module.Flat S (MvPolynomial {j : Fin n // j ≠ k} S ⧸
      Ideal.span ({projectiveDehomogenize S k (MvPolynomial.map c f)} :
        Set (MvPolynomial {j : Fin n // j ≠ k} S))) := by
  rw [← projectiveDehomogenize_scalar_commutes]
  exact polynomial_unit_coefficient_quotient_baseChange_flat c _ q hq

theorem projectiveChart_localized_coefficient_quotient_flat (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    [Algebra R S] [IsLocalization.Away ((projectiveDehomogenize R k f).coeff q) S]
    (c : S →+* T) :
    Module.Flat T (MvPolynomial {j : Fin n // j ≠ k} T ⧸
      Ideal.span ({(projectiveDehomogenize T k
        (MvPolynomial.map (c.comp (algebraMap R S)) f))} :
          Set (MvPolynomial {j : Fin n // j ≠ k} T))) := by
  apply polynomial_unit_coefficient_quotient_flat _ q
  rw [← projectiveDehomogenize_scalar_commutes, MvPolynomial.coeff_map, RingHom.comp_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (S := S)
    ((projectiveDehomogenize R k f).coeff q)).map c

universe u

theorem projectiveChart_unit_coefficient_hypersurface_projection_flat
    {R S : Type u} [CommRing R] [CommRing S] (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    (hq : IsUnit ((projectiveDehomogenize R k f).coeff q)) (c : R →+* S) :
    Flat (polynomialHypersurfaceProjection
      (projectiveDehomogenize S k (MvPolynomial.map c f))) := by
  unfold polynomialHypersurfaceProjection
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr
    (projectiveChart_unit_coefficient_quotient_flat k f q hq c)

theorem projectiveChart_localized_hypersurface_projection_flat
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (k : Fin n)
    (f : MvPolynomial (Fin n) R) (q : {j : Fin n // j ≠ k} →₀ ℕ)
    [Algebra R S] [IsLocalization.Away ((projectiveDehomogenize R k f).coeff q) S]
    (c : S →+* T) :
    Flat (polynomialHypersurfaceProjection (projectiveDehomogenize T k
      (MvPolynomial.map (c.comp (algebraMap R S)) f))) := by
  unfold polynomialHypersurfaceProjection
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr
    (projectiveChart_localized_coefficient_quotient_flat k f q c)

theorem projectiveHomogeneous_chart_flat_hypersurface_cover
    {R : Type u} [CommRing R] (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (p : PrimeSpectrum R)
    (hp : p ∈ polynomialNonzeroLocus f) :
    ∃ q ∈ (projectiveDehomogenize R k f).support,
      (projectiveDehomogenize R k f).coeff q ∉ p.asIdeal ∧
        let S := Localization.Away ((projectiveDehomogenize R k f).coeff q)
        let g := projectiveDehomogenize S k (MvPolynomial.map (algebraMap R S) f)
        g ∈ nonZeroDivisors (MvPolynomial {j : Fin n // j ≠ k} S) ∧
          Flat (polynomialHypersurfaceProjection g) ∧
          LocallyOfFinitePresentation (polynomialHypersurfaceProjection g) ∧
          IsClosedImmersion (polynomialHypersurfaceInclusion g) := by
  rw [← projectiveHomogeneous_nonzeroLocus_chart k d f hf] at hp
  obtain ⟨q, hq, hpq⟩ := polynomialNonzeroLocus_local_coefficient _ p hp
  refine ⟨q, hq, hpq, ?_⟩
  let S := Localization.Away ((projectiveDehomogenize R k f).coeff q)
  have hunit : IsUnit ((projectiveDehomogenize S k
      (MvPolynomial.map (algebraMap R S) f)).coeff q) := by
    rw [← projectiveDehomogenize_scalar_commutes, MvPolynomial.coeff_map]
    exact IsLocalization.Away.algebraMap_isUnit ((projectiveDehomogenize R k f).coeff q)
  exact ⟨finitePolynomial_regular_of_unit_coefficient _ q hunit,
    polynomialHypersurfaceProjection_flat _ q hunit,
    polynomialHypersurfaceProjection_locallyOfFinitePresentation _,
    polynomialHypersurfaceInclusion_isClosedImmersion _⟩

end MixedFujita
