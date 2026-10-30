/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveGlobalScalarFibers
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
The structural morphism on each projective coordinate chart is the scalar
coefficient map. Polynomial affine charts have the categorical scalar
base-change square; the projective square is then checked on the open cover.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

@[reducible]
noncomputable def polynomialProjectiveCoordinateOpenCover (R : Type u) [CommRing R] :
    (polynomialProjectiveScheme n R).OpenCover :=
  Scheme.openCoverOfIsOpenCover _
    (fun k : Fin n => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k))
    (.mk (polynomialProjective_coordinate_opens_cover n R))

theorem polynomialProjectiveCoordinateChart_toBase (R : Type u) [CommRing R] (k : Fin n) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveToBase n R =
      (polynomialProjectiveCoordinateChartIso n R k).hom ≫
        Spec.map (CommRingCat.ofHom (projectiveChartCoefficient R k)) := by
  apply (cancel_epi (polynomialProjectiveCoordinateChartIso n R k).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change Proj.awayι _ _ (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one ≫
      (Proj.toSpecZero _ ≫ Spec.map (polynomialDegreeZeroEquiv n R).symm.toCommRingCatIso.hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

theorem polynomialProjectiveAffineChart_toBase (R : Type u) [CommRing R] (k : Fin n) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveToBase n R =
      (polynomialProjectiveAffineChartIso R k).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial {j : Fin n // j ≠ k} R)) := by
  rw [polynomialProjectiveCoordinateChart_toBase]
  simp only [polynomialProjectiveAffineChartIso, Iso.trans_hom, Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [projectiveChartRingEquiv, projectiveChartAffineToLocalization]

theorem projectiveChartScalarSchemeMap_affine_commutes {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    projectiveChartScalarSchemeMap c k ≫ (polynomialProjectiveAffineChartIso R k).hom =
      (polynomialProjectiveAffineChartIso S k).hom ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.map c :
          MvPolynomial {j : Fin n // j ≠ k} R →+* MvPolynomial {j : Fin n // j ≠ k} S)) := by
  simp only [projectiveChartScalarSchemeMap, polynomialProjectiveAffineChartIso,
    Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change projectiveChartScalarMap c k (projectiveChartAffineToLocalization R k a) =
    projectiveChartAffineToLocalization S k (MvPolynomial.map c a)
  rw [projectiveChartScalarMap, RingHom.comp_apply, RingHom.comp_apply,
    projectiveChartAffine_roundtrip]

theorem mvPolynomialScalar_isPullback {R S : Type u} {σ : Type}
    [CommRing R] [CommRing S] (c : R →+* S) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map c : MvPolynomial σ R →+* MvPolynomial σ S)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial σ S)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)))
      (Spec.map (CommRingCat.ofHom c)) := by
  let : Algebra R S := c.toAlgebra
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ S) := MvPolynomial.algebraMvPolynomial
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R (MvPolynomial σ R) S (MvPolynomial σ S))

theorem projectiveChartScalarMap_coefficient {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    (projectiveChartScalarMap c k).comp (projectiveChartCoefficient R k) =
      (projectiveChartCoefficient S k).comp c := by
  apply RingHom.ext
  intro r
  simp only [RingHom.comp_apply, projectiveChartCoefficient_mk]
  rw [projectiveChartScalarMap_mk c k 0 _ (MvPolynomial.isHomogeneous_C (Fin n) r)]
  simp only [MvPolynomial.map_C]

theorem polynomialScalarProjectiveMap_toBase {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    polynomialScalarProjectiveMap (n := n) c hc ≫ polynomialProjectiveToBase n R =
      polynomialProjectiveToBase n S ≫ Spec.map (CommRingCat.ofHom c) := by
  apply Scheme.Cover.hom_ext (polynomialProjectiveCoordinateOpenCover S)
  intro k
  change (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
      (polynomialScalarProjectiveMap c hc ≫ polynomialProjectiveToBase n R) =
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
      (polynomialProjectiveToBase n S ≫ Spec.map (CommRingCat.ofHom c))
  rw [← Category.assoc, ← projectiveChartScalarSchemeMap_global_commutes c hc k,
    Category.assoc, polynomialProjectiveCoordinateChart_toBase]
  simp only [projectiveChartScalarSchemeMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι,
    polynomialProjectiveCoordinateChart_toBase, Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (projectiveChartScalarMap_coefficient c k)

theorem projectiveChartScalarSchemeMap_isPullback {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    IsPullback (projectiveChartScalarSchemeMap c k)
      ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveToBase n S)
      ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveToBase n R)
      (Spec.map (CommRingCat.ofHom c)) := by
  exact (mvPolynomialScalar_isPullback (R := R) (S := S) (σ := {j : Fin n // j ≠ k}) c).of_iso'
    (polynomialProjectiveAffineChartIso S k) (polynomialProjectiveAffineChartIso R k)
    (Iso.refl _) (Iso.refl _)
    (projectiveChartScalarSchemeMap_affine_commutes c k).symm
    (by simp only [Iso.refl_hom, Category.comp_id];
        exact (polynomialProjectiveAffineChart_toBase S k).symm)
    (by simp only [Iso.refl_hom, Category.comp_id];
        exact (polynomialProjectiveAffineChart_toBase R k).symm)
    (by simp)

theorem polynomialScalarProjectiveMap_preimage_coordinate {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) (k : Fin n) :
    polynomialScalarProjectiveMap c hc ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k) := by
  rw [polynomialScalarProjectiveMap, Proj.map_preimage_basicOpen]
  change Proj.basicOpen _ (MvPolynomial.map c (MvPolynomial.X k)) = _
  rw [MvPolynomial.map_X]

theorem projectiveChartScalarSchemeMap_chart_isPullback {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) (k : Fin n) :
    IsPullback (projectiveChartScalarSchemeMap c k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
      (polynomialScalarProjectiveMap c hc) := by
  apply IsOpenImmersion.isPullback
  · exact (projectiveChartScalarSchemeMap_global_commutes c hc k).symm
  · simp only [Scheme.Opens.opensRange_ι, polynomialScalarProjectiveMap_preimage_coordinate]

theorem polynomialScalarProjectiveMap_isPullback {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    IsPullback (polynomialScalarProjectiveMap (n := n) c hc) (polynomialProjectiveToBase n S)
      (polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (polynomialProjectiveCoordinateOpenCover R)
  intro k
  change IsPullback
    (pullback.snd (polynomialScalarProjectiveMap c hc)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι)
    (pullback.fst _ _ ≫ polynomialProjectiveToBase n S)
    ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι ≫
      polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c))
  let H := (projectiveChartScalarSchemeMap_chart_isPullback c hc k).flip
  exact (projectiveChartScalarSchemeMap_isPullback c k).of_iso H.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd.symm)
    (by simpa only [Iso.refl_hom, Category.comp_id, ← Category.assoc] using
      congrArg (fun f => f ≫ polynomialProjectiveToBase n S) H.isoPullback_hom_fst.symm)
    (by simp) (by simp)

noncomputable def polynomialProjectiveScalarBaseChangeIso {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    polynomialProjectiveScheme n S ≅
      pullback (polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c)) :=
  (polynomialScalarProjectiveMap_isPullback c hc).isoPullback

theorem polynomialProjectiveScalarBaseChangeIso_hom_fst {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    (polynomialProjectiveScalarBaseChangeIso (n := n) c hc).hom ≫ pullback.fst _ _ =
      polynomialScalarProjectiveMap c hc :=
  (polynomialScalarProjectiveMap_isPullback c hc).isoPullback_hom_fst

theorem polynomialProjectiveScalarBaseChangeIso_hom_snd {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    (polynomialProjectiveScalarBaseChangeIso (n := n) c hc).hom ≫ pullback.snd _ _ =
      polynomialProjectiveToBase n S :=
  (polynomialScalarProjectiveMap_isPullback c hc).isoPullback_hom_snd

theorem polynomialParameterProjectiveEval_isPullback {K : Type u} [Field K] (t : K) :
    IsPullback (polynomialParameterProjectiveEval (n := n) t) (polynomialProjectiveToBase n K)
      (polynomialProjectiveToBase n (Polynomial K))
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))) :=
  polynomialScalarProjectiveMap_isPullback (Polynomial.evalRingHom t)
    (fun c => ⟨Polynomial.C c, by simp⟩)

end MixedFujita
