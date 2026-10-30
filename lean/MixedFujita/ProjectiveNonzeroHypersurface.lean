/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHypersurfaceBaseChange

/-!
The canonical restriction of the original global projective hypersurface
to the nonzero residue-field coefficient locus is flat, locally finitely
presented and proper. The proof uses actual coefficient basic opens and
categorical base change, rather than separately reconstructed families.
Relative effective Cartier, Bertini and lct constructions remain separate.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

theorem projectiveHypersurface_coefficient_basicOpen_flat
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) (q : Fin n →₀ ℕ) :
    Flat (projectiveHypersurfaceProjection f d hf ∣_
      (PrimeSpectrum.basicOpen (f.coeff q) : (Spec (CommRingCat.of R)).Opens)) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (f.coeff q))))
  have hrange : g.opensRange =
      (PrimeSpectrum.basicOpen (f.coeff q) : (Spec (CommRingCat.of R)).Opens) :=
    TopologicalSpace.Opens.ext
      (PrimeSpectrum.localization_away_comap_range (Localization.Away (f.coeff q)) (f.coeff q))
  have h : Flat (projectiveHypersurfaceProjection f d hf ∣_ g.opensRange) :=
    (MorphismProperty.arrow_mk_iso_iff (P := @Flat)
      (morphismRestrictOpensRange (projectiveHypersurfaceProjection f d hf) g)).mpr
        (projectiveHypersurface_localization_pullback_flat f d hf q)
  rwa [hrange] at h

theorem polynomial_coefficient_basicOpen_le_nonzeroLocus
    (f : MvPolynomial (Fin n) R) (q : Fin n →₀ ℕ) :
    PrimeSpectrum.basicOpen (f.coeff q) ≤ polynomialNonzeroLocus f := by
  intro p hp
  change ¬ polynomialCoefficientIdeal f ≤ p.asIdeal
  intro h
  exact hp ((polynomialCoefficientIdeal_le_iff f p.asIdeal).mp h q)

noncomputable def projectiveNonzeroHypersurfaceProjection
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    ((projectiveHypersurfaceProjection f d hf) ⁻¹ᵁ
      (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)).toScheme ⟶
        (Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) :=
  projectiveHypersurfaceProjection f d hf ∣_
    (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens)

theorem projectiveNonzeroHypersurfaceProjection_flat
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    Flat (projectiveNonzeroHypersurfaceProjection f d hf) := by
  unfold projectiveNonzeroHypersurfaceProjection
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @Flat)
  intro x
  obtain ⟨q, _, hq⟩ := polynomialNonzeroLocus_local_coefficient f x.val x.property
  let U : (Spec (CommRingCat.of R)).Opens := polynomialNonzeroLocus f
  let B : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen (f.coeff q)
  let W := U.ι ⁻¹ᵁ B
  refine ⟨W, hq, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff (P := @Flat)
    (morphismRestrictRestrict (projectiveHypersurfaceProjection f d hf) U W)).mpr
  have himage : U.ι ''ᵁ W = B := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (polynomial_coefficient_basicOpen_le_nonzeroLocus f q)
  rw [himage]
  exact projectiveHypersurface_coefficient_basicOpen_flat f d hf q

theorem projectiveNonzeroHypersurfaceProjection_locallyOfFinitePresentation
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    LocallyOfFinitePresentation (projectiveNonzeroHypersurfaceProjection f d hf) := by
  let _ := projectiveHypersurfaceProjection_locallyOfFinitePresentation f d hf
  unfold projectiveNonzeroHypersurfaceProjection
  infer_instance

theorem projectiveNonzeroHypersurfaceProjection_isProper
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d) :
    IsProper (projectiveNonzeroHypersurfaceProjection f d hf) := by
  let _ := projectiveHypersurfaceProjection_isProper f d hf
  unfold projectiveNonzeroHypersurfaceProjection
  infer_instance

theorem projectiveNonzeroHypersurfaceProjection_pullback_flat
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    {Y : Scheme.{u}} (g : Y ⟶
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) :
    Flat (pullback.snd (projectiveNonzeroHypersurfaceProjection f d hf) g) := by
  let _ := projectiveNonzeroHypersurfaceProjection_flat f d hf
  infer_instance

theorem projectiveNonzeroHypersurfaceProjection_pullback_locallyOfFinitePresentation
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    {Y : Scheme.{u}} (g : Y ⟶
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) :
    LocallyOfFinitePresentation
      (pullback.snd (projectiveNonzeroHypersurfaceProjection f d hf) g) := by
  let _ := projectiveNonzeroHypersurfaceProjection_locallyOfFinitePresentation f d hf
  infer_instance

theorem projectiveNonzeroHypersurfaceProjection_pullback_isProper
    (f : MvPolynomial (Fin n) R) (d : ℕ) (hf : f.IsHomogeneous d)
    {Y : Scheme.{u}} (g : Y ⟶
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) :
    IsProper (pullback.snd (projectiveNonzeroHypersurfaceProjection f d hf) g) := by
  let _ := projectiveNonzeroHypersurfaceProjection_isProper f d hf
  infer_instance

end MixedFujita
