/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineIdealSheaves
public import MixedFujita.ProjectiveChartFibers

/-!
Actual ideal sheaves on the standard projective coordinate charts.
Scalar maps and the homogeneous-localization overlap maps preserve these
sheaves exactly. Global projective gluing and identification of the maps
with the restrictions of the global Proj maps remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

noncomputable def projectiveChartIdealSheaf (R : Type u) [CommRing R] (k : Fin n)
    (J : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) :
    (polynomialProjectiveCoordinateChart n R k).IdealSheafData :=
  (specIdealSheaf J).comap (polynomialProjectiveCoordinateChartIso n R k).hom

noncomputable def projectiveChartScalarSchemeMap {R S : Type u} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) :
    polynomialProjectiveCoordinateChart n S k ⟶ polynomialProjectiveCoordinateChart n R k :=
  (polynomialProjectiveCoordinateChartIso n S k).hom ≫
    Spec.map (CommRingCat.ofHom (projectiveChartScalarMap c k)) ≫
      (polynomialProjectiveCoordinateChartIso n R k).inv

theorem projectiveChartIdealSheaf_scalar {R S : Type u} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n)
    (J : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) :
    (projectiveChartIdealSheaf R k J).comap (projectiveChartScalarSchemeMap c k) =
      projectiveChartIdealSheaf S k (J.map (projectiveChartScalarMap c k)) := by
  rw [projectiveChartIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  simp only [projectiveChartScalarSchemeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.IdealSheafData.comap_comp, specIdealSheaf_comap]
  rfl

theorem projectiveChartScalarSchemeMap_id (R : Type u) [CommRing R] (k : Fin n) :
    projectiveChartScalarSchemeMap (RingHom.id R) k = 𝟙 _ := by
  simp [projectiveChartScalarSchemeMap, projectiveChartScalarMap_id]

theorem projectiveChartScalarSchemeMap_comp {R S T : Type u}
    [CommRing R] [CommRing S] [CommRing T] (c : R →+* S) (b : S →+* T) (k : Fin n) :
    projectiveChartScalarSchemeMap b k ≫ projectiveChartScalarSchemeMap c k =
      projectiveChartScalarSchemeMap (b.comp c) k := by
  simp only [projectiveChartScalarSchemeMap, Category.assoc, Iso.inv_hom_id_assoc]
  have h : Spec.map (CommRingCat.ofHom (projectiveChartScalarMap b k)) ≫
      Spec.map (CommRingCat.ofHom (projectiveChartScalarMap c k)) =
      Spec.map (CommRingCat.ofHom (projectiveChartScalarMap (b.comp c) k)) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg CommRingCat.ofHom (projectiveChartScalarMap_comp c b k))
  rw [← Category.assoc (Spec.map _) (Spec.map _), h]

noncomputable def projectiveChartOverlapLeftSchemeMap (R : Type u) [CommRing R]
    (k j : Fin n) : Spec (CommRingCat.of (projectiveChartOverlapRing R k j)) ⟶
      polynomialProjectiveCoordinateChart n R k :=
  Spec.map (CommRingCat.ofHom (projectiveChartOverlapFromLeft R k j)) ≫
    (polynomialProjectiveCoordinateChartIso n R k).inv

noncomputable def projectiveChartOverlapRightSchemeMap (R : Type u) [CommRing R]
    (k j : Fin n) : Spec (CommRingCat.of (projectiveChartOverlapRing R k j)) ⟶
      polynomialProjectiveCoordinateChart n R j :=
  Spec.map (CommRingCat.ofHom (projectiveChartOverlapFromRight R k j)) ≫
    (polynomialProjectiveCoordinateChartIso n R j).inv

theorem projectiveChartIdealSheaf_overlap_left (R : Type u) [CommRing R] (k j : Fin n)
    (J : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) :
    (projectiveChartIdealSheaf R k J).comap (projectiveChartOverlapLeftSchemeMap R k j) =
      specIdealSheaf (J.map (projectiveChartOverlapFromLeft R k j)) := by
  rw [projectiveChartIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  simp only [projectiveChartOverlapLeftSchemeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact specIdealSheaf_comap J _

theorem projectiveChartIdealSheaf_overlap_right (R : Type u) [CommRing R] (k j : Fin n)
    (J : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X j))) :
    (projectiveChartIdealSheaf R j J).comap (projectiveChartOverlapRightSchemeMap R k j) =
      specIdealSheaf (J.map (projectiveChartOverlapFromRight R k j)) := by
  rw [projectiveChartIdealSheaf, ← Scheme.IdealSheafData.comap_comp]
  simp only [projectiveChartOverlapRightSchemeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact specIdealSheaf_comap J _

theorem homogeneousChartIdealSheaf_overlap {R : Type u} {ι : Type*} [CommRing R]
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k j : Fin n) :
    (projectiveChartIdealSheaf R k (homogeneousChartLocalizationIdeal I f d hf k)).comap
        (projectiveChartOverlapLeftSchemeMap R k j) =
      (projectiveChartIdealSheaf R j (homogeneousChartLocalizationIdeal I f d hf j)).comap
        (projectiveChartOverlapRightSchemeMap R k j) := by
  rw [projectiveChartIdealSheaf_overlap_left, projectiveChartIdealSheaf_overlap_right,
    homogeneousChartLocalizationIdeal_overlap R k j I f d hf]

end MixedFujita
