/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartEquiv
public import MixedFujita.ProjectiveChartIdealFamily

/-!
The coordinate chart is an actual affine polynomial Scheme. Its homogeneous
localization ideals correspond to the dehomogenized ideals by a ring
isomorphism, including ideal membership and inverse transport. Scalar maps
are transported through the chart isomorphisms and evaluated on every
homogeneous fraction. This does not yet glue relative ideal sheaves or
identify categorical projective fibers.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

noncomputable def polynomialProjectiveAffineChartIso (R : Type*) [CommRing R] (k : Fin n) :
    polynomialProjectiveCoordinateChart n R k ≅
      Spec (CommRingCat.of (MvPolynomial {j : Fin n // j ≠ k} R)) :=
  polynomialProjectiveCoordinateChartIso n R k ≪≫
    Scheme.Spec.mapIso (projectiveChartRingEquiv R k).symm.toCommRingCatIso.op

noncomputable def projectiveChartScalarMap {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+*
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) S)
      (MvPolynomial.X k) :=
  (projectiveChartAffineToLocalization S k).comp
    ((MvPolynomial.map c).comp (projectiveChartLocalizationToAffine R k))

theorem projectiveChartAffineToLocalization_dehomogenize (R : Type*) [CommRing R]
    (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    projectiveChartAffineToLocalization R k (projectiveDehomogenize R k f) =
      HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
        (by simpa using hf) := by
  rw [← projectiveChartLocalizationToAffine_mk R k d f hf,
    projectiveChartLocalization_roundtrip]

theorem projectiveChartScalarMap_mk {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) :
    projectiveChartScalarMap c k
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
        (by simpa using hf)) =
      HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X S k) d
        (MvPolynomial.map c f) (by simpa using hf.map c) := by
  simp only [projectiveChartScalarMap, RingHom.comp_apply]
  rw [projectiveChartLocalizationToAffine_mk R k d f hf,
    projectiveDehomogenize_scalar_commutes,
    projectiveChartAffineToLocalization_dehomogenize S k d _ (hf.map c)]

theorem projectiveChartScalarMap_commutes {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n)
    (x : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) :
    projectiveChartLocalizationToAffine S k (projectiveChartScalarMap c k x) =
      MvPolynomial.map c (projectiveChartLocalizationToAffine R k x) := by
  exact projectiveChartAffine_roundtrip S k _

theorem projectiveChartScalarMap_id (R : Type*) [CommRing R] (k : Fin n) :
    projectiveChartScalarMap (RingHom.id R) k = RingHom.id _ := by
  apply RingHom.ext
  intro x
  change projectiveChartAffineToLocalization R k
    (MvPolynomial.map (RingHom.id R) (projectiveChartLocalizationToAffine R k x)) = x
  simp only [MvPolynomial.map_id]
  exact projectiveChartLocalization_roundtrip R k x

theorem projectiveChartScalarMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (c : R →+* S) (b : S →+* T) (k : Fin n) :
    (projectiveChartScalarMap b k).comp (projectiveChartScalarMap c k) =
      projectiveChartScalarMap (b.comp c) k := by
  apply RingHom.ext
  intro x
  simp only [projectiveChartScalarMap, RingHom.comp_apply, projectiveChartAffine_roundtrip]
  rw [MvPolynomial.map_map]

theorem projectiveChartScalarMap_ideal_commutes {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n)
    (J : Ideal (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k))) :
    Ideal.map (projectiveChartLocalizationToAffine S k) (Ideal.map (projectiveChartScalarMap c k) J) =
      Ideal.map (MvPolynomial.map c) (Ideal.map (projectiveChartLocalizationToAffine R k) J) := by
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun g => Ideal.map g J)
  apply RingHom.ext
  intro x
  exact projectiveChartScalarMap_commutes c k x

noncomputable def homogeneousChartLocalizationIdeal {R ι : Type*} [CommRing R]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)) :=
  Ideal.span (Set.range (fun l : I => HomogeneousLocalization.Away.mk _
    (MvPolynomial.isHomogeneous_X R k) d (f l) (by simpa using hf l l.property)))

theorem homogeneousChartLocalizationIdeal_affine {R ι : Type*} [CommRing R]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal.map (projectiveChartRingEquiv R k).toRingHom
      (homogeneousChartLocalizationIdeal I f d hf k) =
        projectiveChartIdeal k (Ideal.span (Set.range (fun l : I => f l))) := by
  rw [homogeneousChartLocalizationIdeal, Ideal.map_span, ← Set.range_comp',
    projectiveChartIdeal, Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  exact projectiveChartLocalizationToAffine_mk R k d (f l) (hf l l.property)

theorem homogeneousChartLocalizationIdeal_scalar {R S ι : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal.map (projectiveChartScalarMap c k) (homogeneousChartLocalizationIdeal I f d hf k) =
      homogeneousChartLocalizationIdeal I (fun l => MvPolynomial.map c (f l)) d
        (fun l hl => (hf l hl).map c) k := by
  rw [homogeneousChartLocalizationIdeal, Ideal.map_span, ← Set.range_comp',
    homogeneousChartLocalizationIdeal]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  exact projectiveChartScalarMap_mk c k d (f l) (hf l l.property)

theorem homogeneousParameterChartLocalizationIdeal_inverse {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal.map (projectiveChartRingEquiv (Polynomial K) k).symm.toRingHom
      (homogeneousParameterChartIdeal I w p f k) =
        homogeneousParameterChartLocalizationIdeal I w p f d hf k := by
  rw [← homogeneousParameterChartLocalizationIdeal_affine I w p f d hf k,
    Ideal.map_map]
  have heq : (projectiveChartRingEquiv (Polynomial K) k).symm.toRingHom.comp
      (projectiveChartLocalizationToAffine (Polynomial K) k) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    exact projectiveChartLocalization_roundtrip (Polynomial K) k x
  rw [heq, Ideal.map_id]

theorem homogeneousParameterChartLocalizationIdeal_mem_iff {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n)
    (x : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) (Polynomial K)) (MvPolynomial.X k)) :
    x ∈ homogeneousParameterChartLocalizationIdeal I w p f d hf k ↔
      projectiveChartRingEquiv (Polynomial K) k x ∈ homogeneousParameterChartIdeal I w p f k := by
  rw [← homogeneousParameterChartLocalizationIdeal_affine I w p f d hf k]
  exact (Ideal.apply_mem_of_equiv_iff (f := projectiveChartRingEquiv (Polynomial K) k)).symm

end MixedFujita
