/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialHypersurfaceFlat
public import MixedFujita.UniversalOpenProjection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
The actual affine hypersurface Spec(R[X]/(f)), its closed immersion into
polynomial affine space and its coefficient-base projection. A unit
coefficient gives a flat projection. Finite variables give local finite
presentation. These properties are preserved by actual categorical pullback.
The projective relative Cartier gluing and lct statements are separate.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} {σ : Type} [CommRing R]

noncomputable def polynomialHypersurfaceInclusion (f : MvPolynomial σ R) :
    Spec (CommRingCat.of (MvPolynomial σ R ⧸ Ideal.span ({f} : Set (MvPolynomial σ R)))) ⟶
      Spec (CommRingCat.of (MvPolynomial σ R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial σ R)))))

noncomputable def polynomialHypersurfaceProjection (f : MvPolynomial σ R) :
    Spec (CommRingCat.of (MvPolynomial σ R ⧸ Ideal.span ({f} : Set (MvPolynomial σ R)))) ⟶
      Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap R (MvPolynomial σ R ⧸ Ideal.span ({f} : Set (MvPolynomial σ R)))))

theorem polynomialHypersurfaceInclusion_isClosedImmersion (f : MvPolynomial σ R) :
    IsClosedImmersion (polynomialHypersurfaceInclusion f) := by
  unfold polynomialHypersurfaceInclusion
  exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem polynomialHypersurfaceInclusion_projection (f : MvPolynomial σ R) :
    polynomialHypersurfaceInclusion f ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial σ R)) =
      polynomialHypersurfaceProjection f := by
  unfold polynomialHypersurfaceInclusion polynomialHypersurfaceProjection
  rw [← Spec.map_comp]
  congr 1

theorem polynomialHypersurfaceProjection_flat [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q)) :
    Flat (polynomialHypersurfaceProjection f) := by
  unfold polynomialHypersurfaceProjection
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr (polynomial_unit_coefficient_quotient_flat f q hq)

theorem polynomialHypersurfaceProjection_locallyOfFinitePresentation [Finite σ]
    (f : MvPolynomial σ R) :
    LocallyOfFinitePresentation (polynomialHypersurfaceProjection f) := by
  unfold polynomialHypersurfaceProjection
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton f))

theorem polynomialHypersurfaceProjection_pullback_flat [Finite σ]
    (f : MvPolynomial σ R) (q : σ →₀ ℕ) (hq : IsUnit (f.coeff q))
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) :
    Flat (pullback.snd (polynomialHypersurfaceProjection f) g) := by
  let _ := polynomialHypersurfaceProjection_flat f q hq
  infer_instance

theorem polynomialHypersurfaceProjection_pullback_locallyOfFinitePresentation [Finite σ]
    (f : MvPolynomial σ R) {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) :
    LocallyOfFinitePresentation (pullback.snd (polynomialHypersurfaceProjection f) g) := by
  let _ := polynomialHypersurfaceProjection_locallyOfFinitePresentation f
  infer_instance

end MixedFujita
