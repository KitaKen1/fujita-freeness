/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartIdealSheaves

/-!
The homogeneous-localization overlap is the categorical intersection of
the actual standard coordinate charts. Thus the compatibility of their
ideal sheaves is a compatibility on the genuine projective intersection.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem projectiveChartOverlap_isPullback (R : Type*) [CommRing R] (k j : Fin n) :
    IsPullback (projectiveChartOverlapLeftSchemeMap R k j)
      (projectiveChartOverlapRightSchemeMap R k j)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)).ι := by
  let A := MvPolynomial.homogeneousSubmodule (Fin n) R
  let e := Proj.pullbackAwayιIso A (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
    (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one rfl
  have h := (IsPullback.of_hasPullback
    (Proj.awayι A (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one)
    (Proj.awayι A (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one)).of_iso
      e (polynomialProjectiveCoordinateChartIso n R k).symm
      (polynomialProjectiveCoordinateChartIso n R j).symm (Iso.refl _)
      (fst' := projectiveChartOverlapLeftSchemeMap R k j)
      (snd' := projectiveChartOverlapRightSchemeMap R k j)
      (f' := (Proj.basicOpen A (MvPolynomial.X k)).ι)
      (g' := (Proj.basicOpen A (MvPolynomial.X j)).ι)
      (by
        exact (congrArg (fun t => t ≫ (polynomialProjectiveCoordinateChartIso n R k).inv)
          (Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left A
            (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
            (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one rfl)).symm.trans
              (Category.assoc _ _ _))
      (by
        exact (congrArg (fun t => t ≫ (polynomialProjectiveCoordinateChartIso n R j).inv)
          (Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right A
            (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one
            (MvPolynomial.isHomogeneous_X R j) Nat.zero_lt_one rfl)).symm.trans
              (Category.assoc _ _ _))
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; rfl)
      (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]; rfl)
  exact h

noncomputable def projectiveChartIntersectionIso (R : Type*) [CommRing R] (k j : Fin n) :
    Spec (CommRingCat.of (projectiveChartOverlapRing R k j)) ≅
      pullback
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)).ι :=
  (projectiveChartOverlap_isPullback R k j).isoPullback

theorem projectiveChartIntersectionIso_hom_fst (R : Type*) [CommRing R] (k j : Fin n) :
    (projectiveChartIntersectionIso R k j).hom ≫ pullback.fst _ _ =
      projectiveChartOverlapLeftSchemeMap R k j :=
  (projectiveChartOverlap_isPullback R k j).isoPullback_hom_fst

theorem projectiveChartIntersectionIso_hom_snd (R : Type*) [CommRing R] (k j : Fin n) :
    (projectiveChartIntersectionIso R k j).hom ≫ pullback.snd _ _ =
      projectiveChartOverlapRightSchemeMap R k j :=
  (projectiveChartOverlap_isPullback R k j).isoPullback_hom_snd

theorem homogeneousChartIdealSheaf_intersection {R ι : Type*} [CommRing R]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k j : Fin n) :
    (projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k)).comap
        (pullback.fst
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)).ι) =
      (projectiveChartIdealSheaf R j (homogeneousChartLocalizationIdeal I f d hf j)).comap
        (pullback.snd
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j)).ι) := by
  have h := homogeneousChartIdealSheaf_overlap I f d hf k j
  have h' := congrArg (fun L => L.comap (projectiveChartIntersectionIso R k j).inv) h
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartIntersectionIso_hom_fst, ← projectiveChartIntersectionIso_hom_snd] at h'
  simpa only [Iso.inv_hom_id_assoc] using h'

end MixedFujita
