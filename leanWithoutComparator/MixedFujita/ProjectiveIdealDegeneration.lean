/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectivePolynomialMaps

/-!
Closed projective zero loci of the homogeneous parameter ideal and their
inverse images under the actual scalar-evaluation Scheme maps. The zero
parameter gives the monomial locus; the nonzero parameters give diagonal
pullbacks of the original locus. This is a statement about closed subsets,
not yet a relative ideal sheaf, a flat family, or an lct formula.
-/

@[expose] public section

universe u

namespace MixedFujita

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

def polynomialProjectiveIdealLocus {R : Type*} [CommRing R]
    (J : Ideal (MvPolynomial (Fin n) R)) : Set (polynomialProjectiveScheme n R) :=
  ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin n) R) J

theorem polynomialProjectiveIdealLocus_isClosed {R : Type*} [CommRing R]
    (J : Ideal (MvPolynomial (Fin n) R)) : IsClosed (polynomialProjectiveIdealLocus J) :=
  ProjectiveSpectrum.isClosed_zeroLocus _ _

theorem polynomialProjectiveIdealLocus_pullback {R S : Type u} [CommRing R] [CommRing S]
    (g : MvPolynomial.homogeneousSubmodule (Fin n) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin n) S)
    (hg : (MvPolynomial.homogeneousSubmodule (Fin n) S)₊ ≤
      (MvPolynomial.homogeneousSubmodule (Fin n) R)₊.map g)
    (J : Ideal (MvPolynomial (Fin n) R)) :
    (Proj.map g hg) ⁻¹' polynomialProjectiveIdealLocus J =
      polynomialProjectiveIdealLocus (Ideal.map g.toRingHom J) := by
  ext x
  change J ≤ Ideal.comap g.toRingHom x.asHomogeneousIdeal.toIdeal ↔
    Ideal.map g.toRingHom J ≤ x.asHomogeneousIdeal.toIdeal
  exact Ideal.map_le_iff_le_comap.symm

variable {K ι : Type*} [Field K]

def homogeneousParameterProjectiveLocus (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    Set (polynomialProjectiveScheme n (Polynomial K)) :=
  polynomialProjectiveIdealLocus (homogeneousParameterIdeal I w p f)

theorem homogeneousParameterProjectiveLocus_isClosed (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    IsClosed (homogeneousParameterProjectiveLocus I w p f) :=
  polynomialProjectiveIdealLocus_isClosed _

theorem homogeneousParameterProjectiveLocus_eval (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (t : K) :
    (polynomialParameterProjectiveEval (n := n) t) ⁻¹'
      homogeneousParameterProjectiveLocus I w p f =
        polynomialProjectiveIdealLocus
          (Ideal.map (MvPolynomial.map (Polynomial.evalRingHom t))
            (homogeneousParameterIdeal I w p f)) :=
  polynomialProjectiveIdealLocus_pullback _ _ _

theorem homogeneousParameterProjectiveLocus_at_one (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    (polynomialParameterProjectiveEval (n := n) (1 : K)) ⁻¹'
      homogeneousParameterProjectiveLocus I w p f =
        polynomialProjectiveIdealLocus (Ideal.span (Set.range (fun l : I => f l))) := by
  rw [homogeneousParameterProjectiveLocus_eval, homogeneousParameterIdeal_at_one]

theorem homogeneousParameterProjectiveLocus_at_zero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    (polynomialParameterProjectiveEval (n := n) (0 : K)) ⁻¹'
      homogeneousParameterProjectiveLocus I w p f =
        polynomialProjectiveIdealLocus
          (Ideal.span (Set.range (fun l : I => MvPolynomial.monomial (p l) (1 : K)))) := by
  rw [homogeneousParameterProjectiveLocus_eval, homogeneousParameterIdeal_at_zero I w p f hp hw]

theorem homogeneousParameterProjectiveLocus_nonzero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    (polynomialParameterProjectiveEval (n := n) t) ⁻¹'
      homogeneousParameterProjectiveLocus I w p f =
        (polynomialDiagonalProjectiveIso w ht).hom ⁻¹'
          polynomialProjectiveIdealLocus (Ideal.span (Set.range (fun l : I => f l))) := by
  rw [homogeneousParameterProjectiveLocus_eval, homogeneousParameterIdeal_nonzero_fiber I w p f ht hw]
  change polynomialProjectiveIdealLocus _ =
    (polynomialDiagonalProjectiveMap w ht) ⁻¹' polynomialProjectiveIdealLocus _
  unfold polynomialDiagonalProjectiveMap
  exact (polynomialProjectiveIdealLocus_pullback (polynomialDiagonalGradedHom w t)
    (graded_irrelevant_le_map_of_surjective _ (polynomialDiagonalGradedHom_surjective w ht))
    (Ideal.span (Set.range (fun l : I => f l)))).symm

theorem homogeneousParameterProjectiveLocus_closed_image (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) :
    IsClosed ((polynomialProjectiveToBase n (Polynomial K)) ''
      homogeneousParameterProjectiveLocus I w p f) :=
  polynomialProjectiveToBase_closed_image n (Polynomial K)
    (homogeneousParameterProjectiveLocus_isClosed I w p f)

end MixedFujita
