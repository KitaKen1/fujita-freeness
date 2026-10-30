/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartOverlaps

/-!
Scalar fibers of the parameter ideal in the actual homogeneous localization.
The chart ring isomorphism reflects ideal equality, so the monomial fiber
and the original fiber are identified as ideals, preserving multiplicities.
These are ring-theoretic fibers; the relative ideal sheaf and categorical
Scheme fiber identifications remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem projectiveChartIdealMap_injective (R : Type*) [CommRing R] (k : Fin n) :
    Function.Injective (Ideal.map (projectiveChartRingEquiv R k).toRingHom) := by
  intro J L h
  have hh := congrArg (Ideal.map (projectiveChartRingEquiv R k).symm.toRingHom) h
  simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] using hh

noncomputable def projectiveChartMonomialIdeal {R ι : Type*} [CommRing R]
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (k : Fin n) :
    Ideal (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) :=
  Ideal.span (Set.range (fun l : I => (p l).prod (fun i e => projectiveChartCoordinate R k i ^ e)))

theorem projectiveChartMonomialIdeal_affine {R ι : Type*} [CommRing R]
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (k : Fin n) :
    Ideal.map (projectiveChartRingEquiv R k).toRingHom
      (projectiveChartMonomialIdeal (R := R) I p k) =
        Ideal.span (Set.range (fun l : I => (p l).prod (fun i e => projectiveChartVariable R k i ^ e))) := by
  rw [projectiveChartMonomialIdeal, Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  change projectiveChartLocalizationToAffine R k ((p l).prod _) = _
  simp only [map_finsuppProd, map_pow, projectiveChartLocalizationToAffine_coordinate]

theorem homogeneousParameterChartLocalizationIdeal_at_zero {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    Ideal.map (projectiveChartScalarMap (Polynomial.evalRingHom 0) k)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k) =
        projectiveChartMonomialIdeal (R := K) I p k := by
  apply projectiveChartIdealMap_injective K k
  change Ideal.map (projectiveChartLocalizationToAffine K k)
    (Ideal.map (projectiveChartScalarMap (Polynomial.evalRingHom 0) k)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k)) = _
  rw [projectiveChartScalarMap_ideal_commutes,
    homogeneousParameterChartLocalizationIdeal_affine,
    homogeneousParameterChartIdeal_at_zero I w p f k hp hw,
    projectiveChartMonomialIdeal_affine]

theorem homogeneousParameterChartLocalizationIdeal_at_one {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal.map (projectiveChartScalarMap (Polynomial.evalRingHom 1) k)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k) =
        homogeneousChartLocalizationIdeal I f d hf k := by
  apply projectiveChartIdealMap_injective K k
  change Ideal.map (projectiveChartLocalizationToAffine K k)
    (Ideal.map (projectiveChartScalarMap (Polynomial.evalRingHom 1) k)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k)) = _
  rw [projectiveChartScalarMap_ideal_commutes,
    homogeneousParameterChartLocalizationIdeal_affine,
    homogeneousParameterChartIdeal_at_one, homogeneousChartLocalizationIdeal_affine]

theorem projectiveChartMonomialIdeal_eq_top {R ι : Type*} [CommRing R]
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (k : Fin n) (l : I) (d : ℕ)
    (hl : p l = Finsupp.single k d) : projectiveChartMonomialIdeal (R := R) I p k = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h : (p l).prod (fun i e => projectiveChartCoordinate R k i ^ e) ∈
      projectiveChartMonomialIdeal (R := R) I p k := Ideal.subset_span (Set.mem_range_self l)
  simpa [hl, projectiveChartCoordinate_self] using h

end MixedFujita
