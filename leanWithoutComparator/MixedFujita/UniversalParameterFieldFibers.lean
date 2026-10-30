/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveGoodCoefficientFibers
public import MixedFujita.UniversalRelativeCartier

/-!
Evaluate both T and the universal coefficient vector by an actual ring map.
The mapped form is the exact weighted-fiber linear combination; at zero it
is the specified monomial combination and at one the original combination.
Every nonzero such form is an actual closed-subscheme fiber of the restricted
universal family and has a directly constructed relative-Cartier presentation.
One included generator with strict initial weights gives a good vector at
every K-valued T. This does not assert that every vector is good, or supply
Bertini, lct comparison or semicontinuity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {n : ℕ} {K ι : Type u} [Field K]

noncomputable def universalParameterCoefficientEval (t : K) (a : ι → K) :
    MvPolynomial ι (Polynomial K) →+* K :=
  (MvPolynomial.eval₂Hom (RingHom.id K) a).comp
    (MvPolynomial.map (Polynomial.evalRingHom t))

theorem universalParameterCoefficientEval_form
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (t : K) (a : ι → K) :
    MvPolynomial.map (universalParameterCoefficientEval t a)
        (universalParameterHomogeneousForm I w p f) =
      ∑ l ∈ I, MvPolynomial.C (a l) *
        (weightedPolynomialFamily w (p l) (f l)).eval (MvPolynomial.C t) := by
  rw [universalParameterCoefficientEval, ← MvPolynomial.map_map,
    universalParameterHomogeneousForm_baseChange, universalHomogeneousForm_specialize]

theorem universalParameterCoefficientEval_at_zero
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) (a : ι → K) :
    MvPolynomial.map (universalParameterCoefficientEval (0 : K) a)
        (universalParameterHomogeneousForm I w p f) =
      ∑ l ∈ I, MvPolynomial.C (a l) * MvPolynomial.monomial (p l) ((f l).coeff (p l)) := by
  rw [universalParameterCoefficientEval, ← MvPolynomial.map_map,
    universalParameterHomogeneousForm_at_zero I w p f hp hw,
    universalHomogeneousForm_specialize]

theorem universalParameterCoefficientEval_at_one
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) :
    MvPolynomial.map (universalParameterCoefficientEval (1 : K) a)
        (universalParameterHomogeneousForm I w p f) =
      ∑ l ∈ I, MvPolynomial.C (a l) * f l := by
  rw [universalParameterCoefficientEval, ← MvPolynomial.map_map,
    universalParameterHomogeneousForm_at_one, universalHomogeneousForm_specialize]

theorem universalParameterCoefficientEval_exists_good_vector
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) {l : ι} (hl : l ∈ I)
    (hp : p l ∈ (f l).support)
    (hw : ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) (t : K) :
    ∃ a : ι → K, MvPolynomial.map (universalParameterCoefficientEval t a)
      (universalParameterHomogeneousForm I w p f) ≠ 0 := by
  obtain ⟨a, ha⟩ := universalParameterHomogeneousForm_fiber_good_vector I w p f hl hp hw t
  exact ⟨a, by simpa only [universalParameterCoefficientEval, MvPolynomial.map_map] using ha⟩

noncomputable def universalParameterFieldFiberCartierPresentation
    (k₀ : Fin n) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (t : K) (a : ι → K)
    (h0 : MvPolynomial.map (universalParameterCoefficientEval t a)
      (universalParameterHomogeneousForm I w p f) ≠ 0) :
    RelativeCartierPresentation (polynomialProjectiveToBase n K)
      (projectiveHypersurfaceIdealSheaf
        (MvPolynomial.map (universalParameterCoefficientEval t a)
          (universalParameterHomogeneousForm I w p f)) d
        ((universalParameterHomogeneousForm_isHomogeneous I w p f d hf).map
          (universalParameterCoefficientEval t a))) :=
  projectiveFieldHypersurfaceRelativeCartierPresentation K k₀ d _ _ h0

theorem universalParameterFieldFiber_isPullback
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (t : K) (a : ι → K)
    (h0 : MvPolynomial.map (universalParameterCoefficientEval t a)
      (universalParameterHomogeneousForm I w p f) ≠ 0) :
    ∃ m : (projectiveHypersurfaceIdealSheaf
        (MvPolynomial.map (universalParameterCoefficientEval t a)
          (universalParameterHomogeneousForm I w p f)) d
        ((universalParameterHomogeneousForm_isHomogeneous I w p f d hf).map
          (universalParameterCoefficientEval t a))).subscheme ⟶
        (projectiveNonzeroAmbientHypersurfaceIdeal (universalParameterHomogeneousForm I w p f)
          d (universalParameterHomogeneousForm_isHomogeneous I w p f d hf)).subscheme,
      IsPullback m (projectiveHypersurfaceProjection
        (MvPolynomial.map (universalParameterCoefficientEval t a)
          (universalParameterHomogeneousForm I w p f)) d
        ((universalParameterHomogeneousForm_isHomogeneous I w p f d hf).map
          (universalParameterCoefficientEval t a)))
        (projectiveNonzeroCartierProjection (universalParameterHomogeneousForm I w p f) d
          (universalParameterHomogeneousForm_isHomogeneous I w p f d hf))
        (coefficientNonzeroPoint (universalParameterCoefficientEval t a)
          (universalParameterHomogeneousForm I w p f)
          (polynomialNonzeroLocus_eq_top_of_field_nonzero _ h0)) := by
  obtain ⟨m, H, _⟩ := projectiveGoodCoefficientHypersurface_isPullback
    (universalParameterCoefficientEval t a) (universalParameterHomogeneousForm I w p f) d
    (universalParameterHomogeneousForm_isHomogeneous I w p f d hf)
    (polynomialNonzeroLocus_eq_top_of_field_nonzero _ h0)
  exact ⟨m, H⟩

theorem universalParameterFieldFiber_exists_cartier
    (k₀ : Fin n) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {l : ι} (hl : l ∈ I)
    (hp : p l ∈ (f l).support)
    (hw : ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) (t : K) :
    ∃ a : ι → K, MvPolynomial.map (universalParameterCoefficientEval t a)
        (universalParameterHomogeneousForm I w p f) ≠ 0 ∧
      Nonempty (RelativeCartierPresentation (polynomialProjectiveToBase n K)
        (projectiveHypersurfaceIdealSheaf
          (MvPolynomial.map (universalParameterCoefficientEval t a)
            (universalParameterHomogeneousForm I w p f)) d
          ((universalParameterHomogeneousForm_isHomogeneous I w p f d hf).map
            (universalParameterCoefficientEval t a)))) := by
  obtain ⟨a, h0⟩ := universalParameterCoefficientEval_exists_good_vector I w p f hl hp hw t
  exact ⟨a, h0, ⟨universalParameterFieldFiberCartierPresentation k₀ I w p f d hf t a h0⟩⟩

end MixedFujita
