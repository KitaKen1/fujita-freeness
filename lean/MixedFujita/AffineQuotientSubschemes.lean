/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineIdealSheaves
public import MixedFujita.AffineHypersurfaceGeometry

/-!
The actual quotient-ring Spec is the closed subscheme of the actual affine
ideal sheaf, with compatibility of the ambient immersion. This transfers
the already proved hypersurface projection properties to ideal-sheaf
subschemes, preserving the ideal rather than only its zero locus.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

theorem specMap_kernel_idealSheaf {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (Spec.map (CommRingCat.ofHom f)).ker = specIdealSheaf (RingHom.ker f) := by
  rw [Scheme.ker_of_isAffine, specIdealSheaf]
  apply congrArg Scheme.IdealSheafData.ofIdealTop
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
    CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact (Ideal.map_symm (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm

theorem specQuotient_kernel_idealSheaf {R : Type u} [CommRing R] (I : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker = specIdealSheaf I := by
  rw [specMap_kernel_idealSheaf, Ideal.mk_ker]

noncomputable def specQuotientIdealSheafIso {R : Type u} [CommRing R] (I : Ideal R) :
    Spec (CommRingCat.of (R ⧸ I)) ≅ (specIdealSheaf I).subscheme := by
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact asIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toImage ≪≫
    idealSheafSubschemeCongr _ _ (specQuotient_kernel_idealSheaf I)

theorem specQuotientIdealSheafIso_hom_ι {R : Type u} [CommRing R] (I : Ideal R) :
    (specQuotientIdealSheafIso I).hom ≫ (specIdealSheaf I).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  simp only [specQuotientIdealSheafIso, Iso.trans_hom, Category.assoc,
    idealSheafSubschemeCongr_hom_ι, asIso_hom]
  exact Scheme.Hom.toImage_imageι _

theorem polynomialIdealSheafHypersurface_projection_flat {R : Type u} {σ : Type}
    [CommRing R] [Finite σ] (f : MvPolynomial σ R) (q : σ →₀ ℕ)
    (hq : IsUnit (f.coeff q)) :
    Flat ((specIdealSheaf (Ideal.span ({f} : Set (MvPolynomial σ R)))).subschemeι ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (specQuotientIdealSheafIso (Ideal.span ({f} : Set (MvPolynomial σ R)))).hom,
    ← Category.assoc, specQuotientIdealSheafIso_hom_ι]
  exact polynomialHypersurfaceInclusion_projection f ▸ polynomialHypersurfaceProjection_flat f q hq

theorem polynomialIdealSheafHypersurface_projection_locallyOfFinitePresentation
    {R : Type u} {σ : Type} [CommRing R] [Finite σ] (f : MvPolynomial σ R) :
    LocallyOfFinitePresentation
      ((specIdealSheaf (Ideal.span ({f} : Set (MvPolynomial σ R)))).subschemeι ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)
    (specQuotientIdealSheafIso (Ideal.span ({f} : Set (MvPolynomial σ R)))).hom,
    ← Category.assoc, specQuotientIdealSheafIso_hom_ι]
  exact polynomialHypersurfaceInclusion_projection f ▸
    polynomialHypersurfaceProjection_locallyOfFinitePresentation f

end MixedFujita
