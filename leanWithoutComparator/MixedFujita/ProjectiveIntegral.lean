/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHypersurfaceSubschemes
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
Polynomial projective space over an integral domain is integral when it
has a coordinate. The zero homogeneous ideal is an explicit dense point;
the actual affine polynomial charts prove reducedness.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

noncomputable def polynomialProjectiveZeroPoint (R : Type*) [CommRing R] [IsDomain R]
    (k : Fin n) : polynomialProjectiveScheme n R where
  asHomogeneousIdeal := ⊥
  isPrime := by simpa only [HomogeneousIdeal.toIdeal_bot] using
    (inferInstance : (⊥ : Ideal (MvPolynomial (Fin n) R)).IsPrime)
  not_irrelevant_le := by
    intro h
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X R k))
    have hx' : MvPolynomial.X k ∈ (⊥ : Ideal (MvPolynomial (Fin n) R)) := hx
    exact MvPolynomial.X_ne_zero k (Ideal.mem_bot.mp hx')

theorem polynomialProjectiveZeroPoint_closure (R : Type*) [CommRing R] [IsDomain R]
    (k : Fin n) :
    closure ({polynomialProjectiveZeroPoint R k} : Set (polynomialProjectiveScheme n R)) =
      Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  have h : ProjectiveSpectrum.vanishingIdeal
      ({polynomialProjectiveZeroPoint R k} : Set (polynomialProjectiveScheme n R)) = ⊥ := by
    simp [ProjectiveSpectrum.vanishingIdeal, polynomialProjectiveZeroPoint]
  rw [h]
  exact ProjectiveSpectrum.zeroLocus_bot _

theorem polynomialProjectiveScheme_isReduced (R : Type*) [CommRing R] [IsDomain R] :
    IsReduced (polynomialProjectiveScheme n R) := by
  let U := polynomialProjectiveAffineOpenCover (n := n) R
  have : ∀ i, IsReduced (U.X i) := by
    intro i
    change IsReduced (Spec (CommRingCat.of (MvPolynomial {j : Fin n // j ≠ i} R)))
    infer_instance
  exact IsReduced.of_openCover _ U

theorem polynomialProjectiveScheme_isIntegral (R : Type*) [CommRing R] [IsDomain R]
    (k : Fin n) : IsIntegral (polynomialProjectiveScheme n R) := by
  have : IsReduced (polynomialProjectiveScheme n R) := polynomialProjectiveScheme_isReduced R
  have : IrreducibleSpace (polynomialProjectiveScheme n R) := by
    apply (irreducibleSpace_def _).mpr
    simpa only [polynomialProjectiveZeroPoint_closure R k, Set.top_eq_univ] using
      (isIrreducible_singleton (x := polynomialProjectiveZeroPoint R k)).closure
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end MixedFujita
