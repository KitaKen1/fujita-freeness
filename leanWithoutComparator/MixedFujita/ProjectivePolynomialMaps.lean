/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveScheme
public import MixedFujita.HomogeneousIdealFamily
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
Scalar evaluation and invertible diagonal transformations induce actual
Scheme maps on polynomial Proj. The diagonal maps form a Scheme isomorphism.
Evaluation maps are constructed here; an identification with a categorical
base-change fiber is not asserted.
-/

@[expose] public section

universe u

namespace MixedFujita

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

theorem graded_irrelevant_le_map_of_surjective
    {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro d hd x hx
  obtain ⟨a, ha⟩ := hf x
  have heq : f (DirectSum.decompose 𝒜 a d) = x := by
    rw [f.map_directSumDecompose, ha]
    exact DirectSum.decompose_of_mem_same ℬ hx
  rw [← heq]
  exact Ideal.mem_map_of_mem f.toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd (Subtype.property _))

variable {n : ℕ}

noncomputable def polynomialScalarGradedMap {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) :
    MvPolynomial.homogeneousSubmodule (Fin n) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin n) S where
  __ := MvPolynomial.map c
  map_mem hf := hf.map c

theorem polynomialScalarGradedMap_surjective {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (hc : Function.Surjective c) :
    Function.Surjective (polynomialScalarGradedMap (n := n) c) := by
  exact MvPolynomial.map_surjective c hc

noncomputable def polynomialScalarProjectiveMap {R S : Type u} [CommRing R] [CommRing S]
    (c : R →+* S) (hc : Function.Surjective c) :
    polynomialProjectiveScheme n S ⟶ polynomialProjectiveScheme n R :=
  Proj.map (polynomialScalarGradedMap c)
    (graded_irrelevant_le_map_of_surjective _ (polynomialScalarGradedMap_surjective c hc))

variable {K : Type*} [Field K]

noncomputable def polynomialDiagonalGradedHom (w : Fin n → ℕ) (t : K) :
    MvPolynomial.homogeneousSubmodule (Fin n) K →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin n) K where
  __ := polynomialDiagonalHom w t
  map_mem hf := polynomialDiagonalHom_isHomogeneous w t hf

theorem polynomialDiagonalGradedHom_surjective (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    Function.Surjective (polynomialDiagonalGradedHom w t) := by
  intro f
  refine ⟨polynomialDiagonalHom w t⁻¹ f, ?_⟩
  change polynomialDiagonalHom w t (polynomialDiagonalHom w t⁻¹ f) = f
  have h := polynomialDiagonalHom_inverse w (inv_ne_zero ht) f
  simpa only [inv_inv] using h

theorem polynomialDiagonalGradedHom_inverse_comp (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    (polynomialDiagonalGradedHom w t⁻¹).comp (polynomialDiagonalGradedHom w t) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin n) K) := by
  apply GradedRingHom.ext
  intro f
  change polynomialDiagonalHom w t⁻¹ (polynomialDiagonalHom w t f) = f
  exact polynomialDiagonalHom_inverse w ht f

noncomputable def polynomialDiagonalProjectiveMap (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    polynomialProjectiveScheme n K ⟶ polynomialProjectiveScheme n K :=
  Proj.map (polynomialDiagonalGradedHom w t)
    (graded_irrelevant_le_map_of_surjective _ (polynomialDiagonalGradedHom_surjective w ht))

theorem polynomialDiagonalProjectiveMap_inverse_comp (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    polynomialDiagonalProjectiveMap w ht ≫
      polynomialDiagonalProjectiveMap w (inv_ne_zero ht) =
        𝟙 (polynomialProjectiveScheme n K) := by
  unfold polynomialDiagonalProjectiveMap
  have hcomp := polynomialDiagonalGradedHom_inverse_comp w (inv_ne_zero ht)
  simp only [inv_inv] at hcomp
  rw [← Proj.map_comp]
  simp only [hcomp, Proj.map_id]

noncomputable def polynomialDiagonalProjectiveIso (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    polynomialProjectiveScheme n K ≅ polynomialProjectiveScheme n K where
  hom := polynomialDiagonalProjectiveMap w ht
  inv := polynomialDiagonalProjectiveMap w (inv_ne_zero ht)
  hom_inv_id := polynomialDiagonalProjectiveMap_inverse_comp w ht
  inv_hom_id := by
    simpa only [inv_inv] using polynomialDiagonalProjectiveMap_inverse_comp w (inv_ne_zero ht)

noncomputable def polynomialParameterProjectiveEval (t : K) :
    polynomialProjectiveScheme n K ⟶ polynomialProjectiveScheme n (Polynomial K) :=
  polynomialScalarProjectiveMap (Polynomial.evalRingHom t)
    (fun c => ⟨Polynomial.C c, by simp⟩)

end MixedFujita
