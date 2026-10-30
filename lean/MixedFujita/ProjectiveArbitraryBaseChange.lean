/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveBaseChange
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
Polynomial projective space commutes with every coefficient-ring map.
The irrelevant-ideal condition follows from the preserved coordinate
variables, without a surjectivity assumption on the coefficient map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits
open scoped HomogeneousIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem polynomial_irrelevant_le_variables (R : Type*) [CommRing R] :
    (MvPolynomial.homogeneousSubmodule (Fin n) R)₊.toIdeal ≤
      MvPolynomial.idealOfVars (Fin n) R := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd x hx
  change x.IsHomogeneous d at hx
  rw [← pow_one (MvPolynomial.idealOfVars (Fin n) R)]
  apply (MvPolynomial.mem_pow_idealOfVars_iff 1 x).mpr
  intro p hp
  have hdeg : p.degree = d := by
    simpa only [Pi.one_def, ← Finsupp.degree_eq_weight_one] using
      hx (MvPolynomial.mem_support_iff.mp hp)
  omega

theorem polynomialScalarGradedMap_irrelevant {R S : Type*}
    [CommRing R] [CommRing S] (c : R →+* S) :
    (MvPolynomial.homogeneousSubmodule (Fin n) S)₊.toIdeal ≤
      (MvPolynomial.homogeneousSubmodule (Fin n) R)₊.toIdeal.map
        (polynomialScalarGradedMap c).toRingHom := by
  apply (polynomial_irrelevant_le_variables S).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨k, rfl⟩
  rw [← MvPolynomial.map_X c k]
  exact Ideal.mem_map_of_mem (polynomialScalarGradedMap c).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X R k))

noncomputable def polynomialProjectiveCoefficientMap {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    polynomialProjectiveScheme n S ⟶ polynomialProjectiveScheme n R :=
  Proj.map (polynomialScalarGradedMap c) (polynomialScalarGradedMap_irrelevant c)

theorem polynomialCoefficientAwayMap_commutes {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n)
    (b : MvPolynomial (Fin n) S) (hb : b = MvPolynomial.map c (MvPolynomial.X k))
    (hb₁ : b.IsHomogeneous 1)
    (m : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+*
      HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) S) b)
    (hm : ∀ d a (ha : a.IsHomogeneous d),
      m (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d a
        (by simpa using ha)) =
      HomogeneousLocalization.Away.mk _ hb₁ d (MvPolynomial.map c a)
        (by simpa using ha.map c)) :
    Proj.awayι _ b hb₁ Nat.zero_lt_one ≫ polynomialProjectiveCoefficientMap c =
      Spec.map (CommRingCat.ofHom m) ≫
        Proj.awayι _ (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one := by
  subst b
  have hmap : m = HomogeneousLocalization.Away.map (polynomialScalarGradedMap c)
      (MvPolynomial.X k) := by
    apply RingHom.ext
    intro x
    obtain ⟨d, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.isHomogeneous_X R k) x
    rw [hm d a (by simpa using ha)]
    exact (HomogeneousLocalization.Away.map_mk (polynomialScalarGradedMap c)
      (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k) d a ha).symm
  rw [hmap]
  exact Proj.awayι_comp_map (polynomialScalarGradedMap c)
    (polynomialScalarGradedMap_irrelevant c)
    Nat.zero_lt_one (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X R k)

theorem projectiveChartCoefficientMap_global_commutes {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    projectiveChartScalarSchemeMap c k ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι =
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
        polynomialProjectiveCoefficientMap c := by
  apply (cancel_epi (polynomialProjectiveCoordinateChartIso n S k).inv).mp
  simp only [projectiveChartScalarSchemeMap, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]
  change Spec.map (CommRingCat.ofHom (projectiveChartScalarMap c k)) ≫
      Proj.awayι _ _ (MvPolynomial.isHomogeneous_X R k) Nat.zero_lt_one =
    Proj.awayι _ _ (MvPolynomial.isHomogeneous_X S k) Nat.zero_lt_one ≫
      polynomialProjectiveCoefficientMap c
  exact (polynomialCoefficientAwayMap_commutes c k (MvPolynomial.X k)
    (MvPolynomial.map_X c k).symm (MvPolynomial.isHomogeneous_X S k)
    (projectiveChartScalarMap c k) (projectiveChartScalarMap_mk c k)).symm

theorem homogeneousProjectiveIdealSheaf_coefficient {R S : Type u} {ι : Type*}
    [CommRing R] [CommRing S] (c : R →+* S)
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (homogeneousProjectiveIdealSheaf I f d hf).comap (polynomialProjectiveCoefficientMap c) =
      homogeneousProjectiveIdealSheaf I (fun l => MvPolynomial.map c (f l)) d
        (fun l hl => (hf l hl).map c) := by
  apply homogeneousProjectiveIdealSheaf_unique
  intro k
  rw [← Scheme.IdealSheafData.comap_comp,
    ← projectiveChartCoefficientMap_global_commutes c k,
    Scheme.IdealSheafData.comap_comp, homogeneousProjectiveIdealSheaf_restrict,
    projectiveChartIdealSheaf_scalar, homogeneousChartLocalizationIdeal_scalar]

theorem polynomialProjectiveCoefficientMap_toBase {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    polynomialProjectiveCoefficientMap (n := n) c ≫ polynomialProjectiveToBase n R =
      polynomialProjectiveToBase n S ≫ Spec.map (CommRingCat.ofHom c) := by
  apply Scheme.Cover.hom_ext (polynomialProjectiveCoordinateOpenCover S)
  intro k
  change (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
      (polynomialProjectiveCoefficientMap c ≫ polynomialProjectiveToBase n R) =
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι ≫
      (polynomialProjectiveToBase n S ≫ Spec.map (CommRingCat.ofHom c))
  rw [← Category.assoc, ← projectiveChartCoefficientMap_global_commutes c k,
    Category.assoc, polynomialProjectiveCoordinateChart_toBase]
  simp only [projectiveChartScalarSchemeMap, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι,
    polynomialProjectiveCoordinateChart_toBase, Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (projectiveChartScalarMap_coefficient c k)

theorem polynomialProjectiveCoefficientMap_preimage_coordinate {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    polynomialProjectiveCoefficientMap c ⁻¹ᵁ
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k) := by
  rw [polynomialProjectiveCoefficientMap, Proj.map_preimage_basicOpen]
  change Proj.basicOpen _ (MvPolynomial.map c (MvPolynomial.X k)) = _
  rw [MvPolynomial.map_X]

theorem projectiveChartCoefficientMap_chart_isPullback {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (k : Fin n) :
    IsPullback (projectiveChartScalarSchemeMap c k)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) S) (MvPolynomial.X k)).ι
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι
      (polynomialProjectiveCoefficientMap c) := by
  apply IsOpenImmersion.isPullback
  · exact (projectiveChartCoefficientMap_global_commutes c k).symm
  · simp only [Scheme.Opens.opensRange_ι, polynomialProjectiveCoefficientMap_preimage_coordinate]

theorem polynomialProjectiveCoefficientMap_isPullback {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    IsPullback (polynomialProjectiveCoefficientMap (n := n) c) (polynomialProjectiveToBase n S)
      (polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (polynomialProjectiveCoordinateOpenCover R)
  intro k
  change IsPullback
    (pullback.snd (polynomialProjectiveCoefficientMap c)
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι)
    (pullback.fst _ _ ≫ polynomialProjectiveToBase n S)
    ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k)).ι ≫
      polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c))
  let H := (projectiveChartCoefficientMap_chart_isPullback c k).flip
  exact (projectiveChartScalarSchemeMap_isPullback c k).of_iso H.isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using H.isoPullback_hom_snd.symm)
    (by simpa only [Iso.refl_hom, Category.comp_id, ← Category.assoc] using
      congrArg (fun f => f ≫ polynomialProjectiveToBase n S) H.isoPullback_hom_fst.symm)
    (by simp) (by simp)

noncomputable def polynomialProjectiveCoefficientBaseChangeIso {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    polynomialProjectiveScheme n S ≅
      pullback (polynomialProjectiveToBase n R) (Spec.map (CommRingCat.ofHom c)) :=
  (polynomialProjectiveCoefficientMap_isPullback c).isoPullback

theorem polynomialProjectiveCoefficientBaseChangeIso_hom_fst {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    (polynomialProjectiveCoefficientBaseChangeIso (n := n) c).hom ≫ pullback.fst _ _ =
      polynomialProjectiveCoefficientMap c :=
  (polynomialProjectiveCoefficientMap_isPullback c).isoPullback_hom_fst

theorem polynomialProjectiveCoefficientBaseChangeIso_hom_snd {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) :
    (polynomialProjectiveCoefficientBaseChangeIso (n := n) c).hom ≫ pullback.snd _ _ =
      polynomialProjectiveToBase n S :=
  (polynomialProjectiveCoefficientMap_isPullback c).isoPullback_hom_snd

theorem polynomialProjectiveCoefficientMap_eq_surjective {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S) (hc : Function.Surjective c) :
    polynomialProjectiveCoefficientMap (n := n) c = polynomialScalarProjectiveMap c hc := rfl

end MixedFujita
