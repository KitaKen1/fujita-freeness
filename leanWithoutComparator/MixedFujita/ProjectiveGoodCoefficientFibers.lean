/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NonzeroCoefficientPoint

/-!
If a coefficient map makes the polynomial's nonzero locus the entire target
spectrum, polynomial projective space maps into the original ambient base
open. This actual map is a categorical base change of the restricted ambient
projection. Its ideal pullback is exactly the mapped hypersurface ideal,
and that mapped closed subscheme is the actual fiber of the restricted family,
with the projection and ambient immersion preserved.

For any field-valued coefficient map with nonzero mapped form, the condition
is automatic. The mapped hypersurface has a directly reconstructed relative-
Cartier presentation. General invertible-sheaf pullback, arbitrary Scheme base
change of a presentation, Bertini and lct are not asserted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace MixedFujita

universe u

variable {n : ℕ} {R S : Type u} [CommRing R] [CommRing S]

theorem projectiveCoefficientMap_nonzeroAmbient_preimage_top
    (c : R →+* S) (f : MvPolynomial (Fin n) R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    polynomialProjectiveCoefficientMap (n := n) c ⁻¹ᵁ
      ((polynomialProjectiveToBase n R) ⁻¹ᵁ
        (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)) = ⊤ := by
  let U : (Spec (CommRingCat.of R)).Opens := polynomialNonzeroLocus f
  have hc : (Spec.map (CommRingCat.ofHom c)) ⁻¹ᵁ U = ⊤ :=
    (polynomialNonzeroLocus_spec_preimage c f).trans h
  change polynomialProjectiveCoefficientMap c ⁻¹ᵁ
    ((polynomialProjectiveToBase n R) ⁻¹ᵁ U) = ⊤
  calc
    _ = (polynomialProjectiveCoefficientMap c ≫ polynomialProjectiveToBase n R) ⁻¹ᵁ U :=
      (Scheme.Hom.comp_preimage _ _ _).symm
    _ = (polynomialProjectiveToBase n S ≫ Spec.map (CommRingCat.ofHom c)) ⁻¹ᵁ U :=
      congrArg (fun g => g ⁻¹ᵁ U) (polynomialProjectiveCoefficientMap_toBase c)
    _ = polynomialProjectiveToBase n S ⁻¹ᵁ ((Spec.map (CommRingCat.ofHom c)) ⁻¹ᵁ U) :=
      Scheme.Hom.comp_preimage _ _ _
    _ = ⊤ := by rw [hc]; rfl

noncomputable def projectiveGoodCoefficientAmbientMap
    (c : R →+* S) (f : MvPolynomial (Fin n) R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    polynomialProjectiveScheme n S ⟶
      ((polynomialProjectiveToBase n R) ⁻¹ᵁ
        (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).toScheme :=
  schemeOpenFactor (polynomialProjectiveCoefficientMap c) _
    (projectiveCoefficientMap_nonzeroAmbient_preimage_top c f h)

@[reassoc (attr := simp)]
theorem projectiveGoodCoefficientAmbientMap_ι
    (c : R →+* S) (f : MvPolynomial (Fin n) R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    projectiveGoodCoefficientAmbientMap c f h ≫
      ((polynomialProjectiveToBase n R) ⁻¹ᵁ
        (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).ι =
      polynomialProjectiveCoefficientMap c :=
  schemeOpenFactor_ι _ _ _

@[reassoc]
theorem projectiveGoodCoefficientAmbientMap_toBase
    (c : R →+* S) (f : MvPolynomial (Fin n) R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    projectiveGoodCoefficientAmbientMap c f h ≫ projectiveNonzeroAmbientProjection f =
      polynomialProjectiveToBase n S ≫ coefficientNonzeroPoint c f h := by
  apply (cancel_mono (Scheme.Opens.ι (X := Spec (CommRingCat.of R))
    (polynomialNonzeroLocus f))).mp
  rw [Category.assoc, projectiveNonzeroAmbientProjection, morphismRestrict_ι,
    ← Category.assoc, projectiveGoodCoefficientAmbientMap_ι c f h,
    Category.assoc, coefficientNonzeroPoint_ι c f h]
  exact polynomialProjectiveCoefficientMap_toBase (n := n) c

theorem projectiveGoodCoefficientAmbientMap_isPullback
    (c : R →+* S) (f : MvPolynomial (Fin n) R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    IsPullback (projectiveGoodCoefficientAmbientMap c f h) (polynomialProjectiveToBase n S)
      (projectiveNonzeroAmbientProjection f) (coefficientNonzeroPoint c f h) := by
  apply IsPullback.of_right ?_ (projectiveGoodCoefficientAmbientMap_toBase c f h)
    (isPullback_morphismRestrict (polynomialProjectiveToBase n R)
      (polynomialNonzeroLocus f)).flip
  rw [projectiveGoodCoefficientAmbientMap_ι c f h, coefficientNonzeroPoint_ι c f h]
  exact polynomialProjectiveCoefficientMap_isPullback (n := n) c

theorem projectiveGoodCoefficientAmbientMap_ideal
    (c : R →+* S) (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    (projectiveNonzeroAmbientHypersurfaceIdeal f d hf).comap
        (projectiveGoodCoefficientAmbientMap c f h) =
      projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c) := by
  rw [projectiveNonzeroAmbientHypersurfaceIdeal, ← Scheme.IdealSheafData.comap_comp,
    projectiveGoodCoefficientAmbientMap_ι, projectiveHypersurfaceIdealSheaf_coefficient]

theorem projectiveGoodCoefficientHypersurface_isPullback
    (c : R →+* S) (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    ∃ m : (projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c)).subscheme ⟶
        (projectiveNonzeroAmbientHypersurfaceIdeal f d hf).subscheme,
      IsPullback m (projectiveHypersurfaceProjection (MvPolynomial.map c f) d (hf.map c))
        (projectiveNonzeroCartierProjection f d hf) (coefficientNonzeroPoint c f h) ∧
      m ≫ (projectiveNonzeroAmbientHypersurfaceIdeal f d hf).subschemeι =
        (projectiveHypersurfaceIdealSheaf (MvPolynomial.map c f) d (hf.map c)).subschemeι ≫
          projectiveGoodCoefficientAmbientMap c f h := by
  unfold projectiveHypersurfaceProjection
  rw [← projectiveGoodCoefficientAmbientMap_ideal c f d hf h]
  let I := projectiveNonzeroAmbientHypersurfaceIdeal f d hf
  let a := projectiveGoodCoefficientAmbientMap c f h
  let J := I.comap a
  let m := Scheme.IdealSheafData.subschemeMap J I a (I.le_map_comap a)
  have H : IsPullback J.subschemeι m a I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [m]) (by simp [J])
  exact ⟨m, H.flip.paste_vert (projectiveGoodCoefficientAmbientMap_isPullback c f h),
    H.w.symm⟩

noncomputable def projectiveFieldHypersurfaceRelativeCartierPresentation
    (K : Type u) [Field K] (k₀ : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    RelativeCartierPresentation (polynomialProjectiveToBase n K)
      (projectiveHypersurfaceIdealSheaf f d hf) := by
  have hflat : Flat (projectiveHypersurfaceProjection f d hf) := by
    obtain ⟨q, hq⟩ := polynomial_field_nonzero_has_unit_coefficient f h0
    exact projectiveHypersurfaceProjection_flat_of_unit_coefficient f d hf q hq
  exact
    { toInvertibleIdealPresentation :=
        projectiveHypersurfaceInvertibleIdealPresentation K k₀ d f hf h0
      flat := hflat }

end MixedFujita
