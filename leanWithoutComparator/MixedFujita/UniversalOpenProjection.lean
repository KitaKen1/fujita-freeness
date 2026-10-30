/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialNonzeroLocus
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
The actual affine coefficient-parameter projection is open and has a
section for every coefficient vector. Images of open good loci are open.
The good lct locus being open and the Bertini comparison are not inputs
proved by this module.
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

variable {R σ : Type*} [CommRing R]

theorem polynomialNonzeroLocus_eq_projection_basicOpen (f : MvPolynomial σ R) :
    (polynomialNonzeroLocus f : Set (PrimeSpectrum R)) =
      PrimeSpectrum.comap (MvPolynomial.C : R →+* MvPolynomial σ R) ''
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (MvPolynomial σ R))) := by
  rw [MvPolynomial.image_comap_C_basicOpen]
  change (PrimeSpectrum.zeroLocus (polynomialCoefficientIdeal f : Set R))ᶜ = _
  rw [polynomialCoefficientIdeal, PrimeSpectrum.zeroLocus_span]

universe u

noncomputable def universalCoefficientProjection (R ι : Type u) [CommRing R] :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R))

noncomputable def universalCoefficientSection {R ι : Type u} [CommRing R] (a : ι → R) :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (MvPolynomial ι R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id R) a))

theorem universalCoefficientSection_projection {R ι : Type u} [CommRing R] (a : ι → R) :
    universalCoefficientSection a ≫ universalCoefficientProjection R ι =
      𝟙 (Spec (CommRingCat.of R)) := by
  have h : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R) ≫
      CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id R) a) =
        𝟙 (CommRingCat.of R) := by
    ext r
    simp
  unfold universalCoefficientSection universalCoefficientProjection
  rw [← Spec.map_comp, h, Spec.map_id]

theorem universalCoefficientProjection_isOpenMap (R ι : Type u) [CommRing R] :
    IsOpenMap (universalCoefficientProjection R ι) :=
  MvPolynomial.isOpenMap_comap_C

noncomputable def universalCoefficientOpenImage {R ι : Type u} [CommRing R]
    (U : (Spec (CommRingCat.of (MvPolynomial ι R))).Opens) :
    (Spec (CommRingCat.of R)).Opens :=
  ⟨universalCoefficientProjection R ι '' (U : Set _),
    universalCoefficientProjection_isOpenMap R ι _ U.isOpen⟩

theorem universalCoefficientOpenImage_mem {R ι : Type u} [CommRing R]
    (U : (Spec (CommRingCat.of (MvPolynomial ι R))).Opens)
    (x : Spec (CommRingCat.of R)) :
    x ∈ universalCoefficientOpenImage U ↔
      ∃ y ∈ U, universalCoefficientProjection R ι y = x :=
  Iff.rfl

theorem universalCoefficientOpenImage_contains_section {R ι : Type u} [CommRing R]
    (U : (Spec (CommRingCat.of (MvPolynomial ι R))).Opens) (a : ι → R)
    (x : Spec (CommRingCat.of R)) (hx : universalCoefficientSection a x ∈ U) :
    x ∈ universalCoefficientOpenImage U := by
  refine ⟨universalCoefficientSection a x, hx, ?_⟩
  have h := universalCoefficientSection_projection a
  exact congrArg (fun f => f x) h

end MixedFujita
