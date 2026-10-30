/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedCoefficientDegeneration
public import MixedFujita.PolynomialParameterOpen
public import MixedFujita.ProjectiveNonzeroFibers

/-!
The fixed-coefficient, one-parameter hypersurface has an actual relative-
Cartier presentation on its nonzero coefficient open if its zero fiber is
nonzero. Its nonzero field fibers are categorical fibers. At nonzero T,
the corrected original linear combination gives an isomorphic closed
subscheme over Spec K, preserving the ambient diagonal map.

The good-parameter selection theorem uses an explicitly closed bad locus
on the restricted projective ambient. It does not supply Bertini, klt
openness or threshold semicontinuity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

variable {n : ℕ} {K ι : Type u} [Field K]

noncomputable def fixedCoefficientRelativeCartierPresentation
    (k₀ : Fin n) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d)
    (hzero : MvPolynomial.map (Polynomial.evalRingHom 0)
      (fixedCoefficientParameterForm I w p f a) ≠ 0) :
    RelativeCartierPresentation
      (projectiveNonzeroAmbientProjection (fixedCoefficientParameterForm I w p f a))
      (projectiveNonzeroAmbientHypersurfaceIdeal (fixedCoefficientParameterForm I w p f a) d
        (fixedCoefficientParameterForm_isHomogeneous I w p f a d hf)) :=
  projectiveNonzeroRelativeCartierPresentation (Polynomial K) k₀ d _ _
    (fixedCoefficientParameterForm_ne_zero_of_fiber I w p f a 0 hzero)

noncomputable def fixedCoefficientFieldFiberCartierPresentation
    (k₀ : Fin n) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (t : K)
    (h0 : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p f a) ≠ 0) :
    RelativeCartierPresentation (polynomialProjectiveToBase n K)
      (projectiveHypersurfaceIdealSheaf
        (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
        ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
          (Polynomial.evalRingHom t))) :=
  projectiveFieldHypersurfaceRelativeCartierPresentation K k₀ d _ _ h0

theorem fixedCoefficientFieldFiber_isPullback
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (t : K)
    (h0 : MvPolynomial.map (Polynomial.evalRingHom t)
      (fixedCoefficientParameterForm I w p f a) ≠ 0) :
    ∃ m : (projectiveHypersurfaceIdealSheaf
        (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
        ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
          (Polynomial.evalRingHom t))).subscheme ⟶
        (projectiveNonzeroAmbientHypersurfaceIdeal (fixedCoefficientParameterForm I w p f a) d
          (fixedCoefficientParameterForm_isHomogeneous I w p f a d hf)).subscheme,
      IsPullback m (projectiveHypersurfaceProjection
        (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
        ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
          (Polynomial.evalRingHom t)))
        (projectiveNonzeroCartierProjection (fixedCoefficientParameterForm I w p f a) d
          (fixedCoefficientParameterForm_isHomogeneous I w p f a d hf))
        (coefficientNonzeroPoint (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)
          (polynomialNonzeroLocus_eq_top_of_field_nonzero _ h0)) ∧
      m ≫ (projectiveNonzeroAmbientHypersurfaceIdeal (fixedCoefficientParameterForm I w p f a) d
          (fixedCoefficientParameterForm_isHomogeneous I w p f a d hf)).subschemeι =
        (projectiveHypersurfaceIdealSheaf
          (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
          ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
            (Polynomial.evalRingHom t))).subschemeι ≫
          projectiveGoodCoefficientAmbientMap (Polynomial.evalRingHom t)
            (fixedCoefficientParameterForm I w p f a)
            (polynomialNonzeroLocus_eq_top_of_field_nonzero _ h0) :=
  projectiveGoodCoefficientHypersurface_isPullback _ _ _ _ _

theorem polynomialLinearCombination_isHomogeneous
    (I : Finset ι) (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) :
    (∑ l ∈ I, MvPolynomial.C (a l) * f l).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  exact fun l hl => (hf l hl).C_mul _

theorem projectiveHypersurfaceIdealSheaf_diagonal
    (f : MvPolynomial (Fin n) K) (d : ℕ) (hf : f.IsHomogeneous d)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) :
    (projectiveHypersurfaceIdealSheaf f d hf).comap (polynomialDiagonalProjectiveMap w ht) =
      projectiveHypersurfaceIdealSheaf (polynomialDiagonalHom w t f) d
        (polynomialDiagonalHom_isHomogeneous w t hf) :=
  homogeneousProjectiveIdealSheaf_diagonal ({()} : Finset Unit) (fun _ => f) d
    (fun _ _ => hf) w ht

theorem projectiveHypersurfaceDiagonalSubscheme_iso
    (f : MvPolynomial (Fin n) K) (d : ℕ) (hf : f.IsHomogeneous d)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0)
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (hEq : F = polynomialDiagonalHom w t f) :
    ∃ e : (projectiveHypersurfaceIdealSheaf F d hF).subscheme ≅
        (projectiveHypersurfaceIdealSheaf f d hf).subscheme,
      e.hom ≫ (projectiveHypersurfaceIdealSheaf f d hf).subschemeι =
        (projectiveHypersurfaceIdealSheaf F d hF).subschemeι ≫
            (polynomialDiagonalProjectiveIso w ht).hom ∧
      e.hom ≫ projectiveHypersurfaceProjection f d hf =
        projectiveHypersurfaceProjection F d hF := by
  subst F
  unfold projectiveHypersurfaceProjection
  rw [← projectiveHypersurfaceIdealSheaf_diagonal f d hf w ht]
  obtain ⟨e, he⟩ := idealSheaf_comap_iso_subscheme
    (projectiveHypersurfaceIdealSheaf f d hf) (polynomialDiagonalProjectiveIso w ht)
  refine ⟨e, he, ?_⟩
  change e.hom ≫ (projectiveHypersurfaceIdealSheaf f d hf).subschemeι ≫
    polynomialProjectiveToBase n K = _
  rw [← Category.assoc, he, Category.assoc]
  change _ ≫ (polynomialDiagonalProjectiveMap w ht ≫ polynomialProjectiveToBase n K) = _
  rw [polynomialDiagonalProjectiveMap_toBase]
  rfl

theorem fixedCoefficientFieldFiber_diagonal_subscheme_iso
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    ∃ e : (projectiveHypersurfaceIdealSheaf
        (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
        ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
          (Polynomial.evalRingHom t))).subscheme ≅
        (projectiveHypersurfaceIdealSheaf
          (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) d
          (polynomialLinearCombination_isHomogeneous I f _ d hf)).subscheme,
      e.hom ≫ (projectiveHypersurfaceIdealSheaf
          (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) d
          (polynomialLinearCombination_isHomogeneous I f _ d hf)).subschemeι =
        (projectiveHypersurfaceIdealSheaf
          (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
          ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
            (Polynomial.evalRingHom t))).subschemeι ≫ (polynomialDiagonalProjectiveIso w ht).hom ∧
      e.hom ≫ projectiveHypersurfaceProjection
          (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) d
          (polynomialLinearCombination_isHomogeneous I f _ d hf) =
        projectiveHypersurfaceProjection
          (MvPolynomial.map (Polynomial.evalRingHom t) (fixedCoefficientParameterForm I w p f a)) d
          ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
            (Polynomial.evalRingHom t)) := by
  exact projectiveHypersurfaceDiagonalSubscheme_iso
    (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) d
    (polynomialLinearCombination_isHomogeneous I f (correctedCoefficientVector w p a t) d hf)
    w ht _ ((fixedCoefficientParameterForm_isHomogeneous I w p f a d hf).map
      (Polynomial.evalRingHom t))
    (fixedCoefficientParameterForm_nonzero_parameter_diagonal I w p f a ht hw)

end MixedFujita
