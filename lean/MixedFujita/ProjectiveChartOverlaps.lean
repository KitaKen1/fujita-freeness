/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveAffineCharts

/-!
On a coordinate overlap, equal-degree sections divided by X_k^d or X_j^d
are related by a common unit. Consequently their generated ideals agree.
This supplies algebraic overlap compatibility, not an already glued
relative ideal sheaf or categorical fiber identification.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} (R : Type*) [CommRing R] (k j : Fin n)

@[reducible]
noncomputable def projectiveChartOverlapRing : Type _ :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
    (MvPolynomial.X k * MvPolynomial.X j)

noncomputable def projectiveChartOverlapFromLeft :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+* projectiveChartOverlapRing R k j :=
  HomogeneousLocalization.awayMap _ (MvPolynomial.isHomogeneous_X R j) rfl

noncomputable def projectiveChartOverlapFromRight :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X j) →+* projectiveChartOverlapRing R k j :=
  HomogeneousLocalization.awayMap _ (MvPolynomial.isHomogeneous_X R k) (mul_comm _ _)

noncomputable def projectiveChartOverlapUnit : projectiveChartOverlapRing R k j :=
  projectiveChartOverlapFromLeft R k j (projectiveChartCoordinate R k j)

noncomputable def projectiveChartOverlapUnitInverse : projectiveChartOverlapRing R k j :=
  projectiveChartOverlapFromRight R k j (projectiveChartCoordinate R j k)

theorem projectiveChartOverlapUnit_mul_inverse :
    projectiveChartOverlapUnit R k j * projectiveChartOverlapUnitInverse R k j = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveChartOverlapUnit, projectiveChartOverlapUnitInverse,
    projectiveChartOverlapFromLeft, projectiveChartOverlapFromRight,
    projectiveChartCoordinate, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, pow_one, mul_one]
  ring

theorem projectiveChartOverlapUnit_isUnit : IsUnit (projectiveChartOverlapUnit R k j) :=
  isUnit_iff_exists_inv.mpr ⟨projectiveChartOverlapUnitInverse R k j,
    projectiveChartOverlapUnit_mul_inverse R k j⟩

theorem projectiveChartOverlap_fraction (d : ℕ) (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous d) :
    projectiveChartOverlapFromLeft R k j
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
        (by simpa using hf)) =
      projectiveChartOverlapUnit R k j ^ d *
        projectiveChartOverlapFromRight R k j
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R j) d f
            (by simpa using hf)) := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveChartOverlapUnit, projectiveChartOverlapFromLeft,
    projectiveChartOverlapFromRight, projectiveChartCoordinate,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
    SubmonoidClass.coe_pow, pow_one]
  ring

theorem ideal_span_range_unit_mul {A ι : Type*} [CommRing A] (u : A) (hu : IsUnit u)
    (f : ι → A) : Ideal.span (Set.range (fun i => u * f i)) = Ideal.span (Set.range f) := by
  simp only [Ideal.span_range_eq_iSup, Ideal.span_singleton_mul_left_unit hu]

theorem homogeneousChartLocalizationIdeal_overlap {ι : Type*} (I : Finset ι)
    (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    Ideal.map (projectiveChartOverlapFromLeft R k j)
      (homogeneousChartLocalizationIdeal I f d hf k) =
    Ideal.map (projectiveChartOverlapFromRight R k j)
      (homogeneousChartLocalizationIdeal I f d hf j) := by
  rw [homogeneousChartLocalizationIdeal, homogeneousChartLocalizationIdeal,
    Ideal.map_span, Ideal.map_span, ← Set.range_comp', ← Set.range_comp']
  have heq : (fun l : I => projectiveChartOverlapFromLeft R k j
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d (f l)
        (by simpa using hf l l.property))) =
      (fun l : I => projectiveChartOverlapUnit R k j ^ d *
        projectiveChartOverlapFromRight R k j
          (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R j) d (f l)
            (by simpa using hf l l.property))) := by
    funext l
    exact projectiveChartOverlap_fraction R k j d (f l) (hf l l.property)
  exact (congrArg (fun g : I → projectiveChartOverlapRing R k j => Ideal.span (Set.range g))
    heq).trans (ideal_span_range_unit_mul _ (projectiveChartOverlapUnit_isUnit R k j |>.pow d) _)

theorem homogeneousParameterChartLocalizationIdeal_overlap {K ι : Type*} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k j : Fin n) :
    Ideal.map (projectiveChartOverlapFromLeft (Polynomial K) k j)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k) =
    Ideal.map (projectiveChartOverlapFromRight (Polynomial K) k j)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf j) :=
  homogeneousChartLocalizationIdeal_overlap (Polynomial K) k j I
    (fun l => homogeneousParameterFamily w (p l) (f l)) d
    (fun l hl => homogeneousParameterFamily_isHomogeneous w (p l) (hf l hl))

end MixedFujita
