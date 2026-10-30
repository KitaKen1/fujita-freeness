/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.OpenIdealGluing
public import MixedFujita.ProjectiveChartSubschemes

/-!
Compatible equal-degree homogeneous ideals glue to an actual ideal sheaf
on polynomial Proj. The construction has exact coordinate-chart restrictions
and is unique. The homogeneous parameter family is constructed globally,
with each of its chart closed subschemes identified as an actual pullback.
Ambient coefficient base change and the exceptional-divisor comparison are
separate obligations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

@[reducible]
noncomputable def polynomialProjectiveCoordinateAffineOpen (R : Type u) [CommRing R]
    (k : Fin n) : (polynomialProjectiveScheme n R).affineOpens :=
  ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k),
    Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one⟩

theorem polynomialProjectiveCoordinateChart_isAffine (R : Type u) [CommRing R]
    (k : Fin n) : IsAffine (polynomialProjectiveCoordinateChart n R k) :=
  IsAffine.of_isIso (polynomialProjectiveCoordinateChartIso n R k).hom

theorem polynomialProjectiveCoordinateChart_quasiCompact (R : Type u) [CommRing R]
    (k : Fin n) : QuasiCompact
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι := by
  have : IsAffine (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)).toScheme := polynomialProjectiveCoordinateChart_isAffine R k
  exact quasiCompact_of_compactSpace _

noncomputable def homogeneousProjectiveIdealSheaf {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (polynomialProjectiveScheme n R).IdealSheafData :=
  finiteOpenIdealGlue (polynomialProjectiveCoordinateChart n R)
    (fun k => (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k)).ι)
    (fun k => projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k))

theorem homogeneousProjectiveIdealSheaf_restrict {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    (homogeneousProjectiveIdealSheaf I f d hf).comap
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι =
      projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k) := by
  have : ∀ j : Fin n, QuasiCompact
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)).ι :=
    polynomialProjectiveCoordinateChart_quasiCompact R
  apply finiteOpenIdealGlue_restrict
  exact fun i j => (homogeneousChartIdealSheaf_intersection I f d hf j i).symm

theorem homogeneousProjectiveIdealSheaf_unique {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d)
    (J : (polynomialProjectiveScheme n R).IdealSheafData)
    (hJ : ∀ k : Fin n, J.comap
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι =
      projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k)) :
    J = homogeneousProjectiveIdealSheaf I f d hf := by
  apply idealSheaf_ext_of_affine_restrictions J _
    (polynomialProjectiveCoordinateAffineOpen R)
    (polynomialProjective_coordinate_opens_cover n R)
  exact fun k => (hJ k).trans (homogeneousProjectiveIdealSheaf_restrict I f d hf k).symm

noncomputable def homogeneousParameterProjectiveIdealSheaf {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (polynomialProjectiveScheme n (Polynomial K)).IdealSheafData :=
  homogeneousProjectiveIdealSheaf I (fun l => homogeneousParameterFamily w (p l) (f l)) d
    (fun l hl => homogeneousParameterFamily_isHomogeneous w (p l) (hf l hl))

theorem homogeneousParameterProjectiveIdealSheaf_restrict {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    (homogeneousParameterProjectiveIdealSheaf I w p f d hf).comap
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) (Polynomial K))
          (MvPolynomial.X k)).ι =
      homogeneousParameterChartIdealSheaf I w p f d hf k := by
  exact homogeneousProjectiveIdealSheaf_restrict I
    (fun l => homogeneousParameterFamily w (p l) (f l)) d
    (fun l hl => homogeneousParameterFamily_isHomogeneous w (p l) (hf l hl)) k

theorem homogeneousProjectiveChartSubscheme_pullback {R : Type u} [CommRing R] {ι : Type*}
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    ∃ e : (projectiveChartIdealSheaf R k
        (homogeneousChartLocalizationIdeal I f d hf k)).subscheme ≅
      pullback
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
        (homogeneousProjectiveIdealSheaf I f d hf).subschemeι,
      e.hom ≫ pullback.fst _ _ =
        (projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k)).subschemeι := by
  rw [← homogeneousProjectiveIdealSheaf_restrict I f d hf k]
  exact ⟨(homogeneousProjectiveIdealSheaf I f d hf).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

theorem homogeneousParameterProjectiveChartSubscheme_pullback {K ι : Type u} [Field K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    ∃ e : (homogeneousParameterChartIdealSheaf I w p f d hf k).subscheme ≅
      pullback
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) (Polynomial K))
          (MvPolynomial.X k)).ι
        (homogeneousParameterProjectiveIdealSheaf I w p f d hf).subschemeι,
      e.hom ≫ pullback.fst _ _ =
        (homogeneousParameterChartIdealSheaf I w p f d hf k).subschemeι := by
  rw [← homogeneousParameterProjectiveIdealSheaf_restrict I w p f d hf k]
  exact ⟨(homogeneousParameterProjectiveIdealSheaf I w p f d hf).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

end MixedFujita
