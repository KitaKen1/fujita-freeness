/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveArbitraryBaseChange
public import MixedFujita.ProjectiveHypersurfaceSubschemes

/-!
The mapped homogeneous hypersurface is the actual categorical coefficient
base change, with both projections and ambient immersions preserved.
Coefficient localization therefore proves flatness of the original family
on each coefficient basic open. Relative Cartier and lct remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

theorem projectiveIdealSheafCoefficientSubscheme_baseChange {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S)
    (I : (polynomialProjectiveScheme n R).IdealSheafData) :
    ∃ (m : (I.comap (polynomialProjectiveCoefficientMap c)).subscheme ⟶ I.subscheme)
      (e : (I.comap (polynomialProjectiveCoefficientMap c)).subscheme ≅
        pullback (I.subschemeι ≫ polynomialProjectiveToBase n R)
          (Spec.map (CommRingCat.ofHom c))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        (I.comap (polynomialProjectiveCoefficientMap c)).subschemeι ≫
          polynomialProjectiveToBase n S ∧
      m ≫ I.subschemeι =
        (I.comap (polynomialProjectiveCoefficientMap c)).subschemeι ≫
          polynomialProjectiveCoefficientMap c := by
  let J := I.comap (polynomialProjectiveCoefficientMap c)
  let m := Scheme.IdealSheafData.subschemeMap J I (polynomialProjectiveCoefficientMap c)
    (I.le_map_comap (polynomialProjectiveCoefficientMap c))
  have h : IsPullback J.subschemeι m (polynomialProjectiveCoefficientMap c) I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [m]) (by simp [J])
  have H := h.flip.paste_vert (polynomialProjectiveCoefficientMap_isPullback c)
  exact ⟨m, H.isoPullback, H.isoPullback_hom_fst, H.isoPullback_hom_snd,
    by simpa only [J] using h.w.symm⟩

theorem projectiveHypersurfaceIdealSheaf_coefficient {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    (projectiveHypersurfaceIdealSheaf f d hf).comap (polynomialProjectiveCoefficientMap c) =
      projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c) :=
  homogeneousProjectiveIdealSheaf_coefficient c _ _ d _

theorem projectiveHypersurface_coefficient_baseChange {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    ∃ (m : (projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c)).subscheme ⟶
        (projectiveHypersurfaceIdealSheaf f d hf).subscheme)
      (e : (projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c)).subscheme ≅
        pullback (projectiveHypersurfaceProjection f d hf) (Spec.map (CommRingCat.ofHom c))),
      e.hom ≫ pullback.fst _ _ = m ∧
      e.hom ≫ pullback.snd _ _ =
        projectiveHypersurfaceProjection (MvPolynomial.map c f) d (hf.map c) ∧
      m ≫ (projectiveHypersurfaceIdealSheaf f d hf).subschemeι =
        (projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c)).subschemeι ≫
          polynomialProjectiveCoefficientMap c := by
  unfold projectiveHypersurfaceProjection
  rw [← projectiveHypersurfaceIdealSheaf_coefficient c f d hf]
  exact projectiveIdealSheafCoefficientSubscheme_baseChange c _

theorem projectiveHypersurface_coefficient_pullback_flat {R S : Type u}
    [CommRing R] [CommRing S] (c : R →+* S)
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (q : Fin n →₀ ℕ) (hq : IsUnit (c (f.coeff q))) :
    Flat (pullback.snd (projectiveHypersurfaceProjection f d hf)
      (Spec.map (CommRingCat.ofHom c))) := by
  obtain ⟨m, e, _, he, _⟩ := projectiveHypersurface_coefficient_baseChange c f d hf
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat) e.hom, he]
  apply projectiveHypersurfaceProjection_flat_of_unit_coefficient _ d (hf.map c) q
  simpa only [MvPolynomial.coeff_map] using hq

theorem projectiveHypersurface_localization_pullback_flat {R : Type u} [CommRing R]
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (q : Fin n →₀ ℕ) :
    Flat (pullback.snd (projectiveHypersurfaceProjection f d hf)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f.coeff q)))))) :=
  projectiveHypersurface_coefficient_pullback_flat _ f d hf q
    (IsLocalization.Away.algebraMap_isUnit (f.coeff q))

end MixedFujita
