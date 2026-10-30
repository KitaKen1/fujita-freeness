/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafOpenBaseRestriction

/-!
The actual pulled-back hypersurface ideal on the ambient projective Scheme
over the nonzero coefficient locus. Its closed-subscheme projection is
identified with the canonical nonzero-locus family, so its flatness, properness
and local finite presentation are proved over arbitrary coefficient rings.

Over an integral domain, a nonzero homogeneous equation additionally supplies
an actual invertible module sheaf with an injective structure-sheaf inclusion
whose affine image is exactly this ideal. Combining this with proved flatness
constructs RelativeCartierPresentation; no relative-Cartier conclusion is
assumed as input. This does not prove preservation of the presentation under
arbitrary non-open base change or construct the later Bertini/lct data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

noncomputable def projectiveNonzeroAmbientProjection (f : MvPolynomial (Fin n) R) :
    ((polynomialProjectiveToBase n R) ⁻¹ᵁ
      (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).toScheme ⟶
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f) :=
  polynomialProjectiveToBase n R ∣_
    (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)

noncomputable def projectiveNonzeroAmbientHypersurfaceIdeal
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    (((polynomialProjectiveToBase n R) ⁻¹ᵁ
      (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).toScheme).IdealSheafData :=
  (projectiveHypersurfaceIdealSheaf f d hf).comap
    ((polynomialProjectiveToBase n R) ⁻¹ᵁ
      (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).ι

noncomputable def projectiveNonzeroCartierProjection
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    (projectiveNonzeroAmbientHypersurfaceIdeal f d hf).subscheme ⟶
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f) :=
  (projectiveNonzeroAmbientHypersurfaceIdeal f d hf).subschemeι ≫
    projectiveNonzeroAmbientProjection f

theorem projectiveNonzeroCartierProjection_isPullback
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    IsPullback
      (idealSheafOpenBaseRestrictionMap (polynomialProjectiveToBase n R)
        (projectiveHypersurfaceIdealSheaf f d hf) (polynomialNonzeroLocus f))
      (projectiveNonzeroCartierProjection f d hf)
      (projectiveHypersurfaceProjection f d hf)
      (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) :=
  idealSheafOpenBaseRestriction_isPullback _ _ _

theorem projectiveNonzeroCartierProjection_flat
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    Flat (projectiveNonzeroCartierProjection f d hf) :=
  idealSheafOpenBaseRestriction_property (polynomialProjectiveToBase n R)
    (projectiveHypersurfaceIdealSheaf f d hf) (polynomialNonzeroLocus f) (@Flat)
    (projectiveNonzeroHypersurfaceProjection_flat f d hf)

theorem projectiveNonzeroCartierProjection_locallyOfFinitePresentation
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    LocallyOfFinitePresentation (projectiveNonzeroCartierProjection f d hf) :=
  idealSheafOpenBaseRestriction_property (polynomialProjectiveToBase n R)
    (projectiveHypersurfaceIdealSheaf f d hf) (polynomialNonzeroLocus f)
    (@LocallyOfFinitePresentation)
    (projectiveNonzeroHypersurfaceProjection_locallyOfFinitePresentation f d hf)

theorem projectiveNonzeroCartierProjection_isProper
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    IsProper (projectiveNonzeroCartierProjection f d hf) :=
  idealSheafOpenBaseRestriction_property (polynomialProjectiveToBase n R)
    (projectiveHypersurfaceIdealSheaf f d hf) (polynomialNonzeroLocus f) (@IsProper)
    (projectiveNonzeroHypersurfaceProjection_isProper f d hf)

noncomputable def projectiveNonzeroRelativeCartierPresentation
    (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    RelativeCartierPresentation (projectiveNonzeroAmbientProjection f)
      (projectiveNonzeroAmbientHypersurfaceIdeal f d hf) :=
  { toInvertibleIdealPresentation :=
      projectiveHypersurfaceOpenInvertibleIdealPresentation R k₀ d f hf h0
        ((polynomialProjectiveToBase n R) ⁻¹ᵁ
          (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).ι
    flat := projectiveNonzeroCartierProjection_flat f d hf }

end MixedFujita
