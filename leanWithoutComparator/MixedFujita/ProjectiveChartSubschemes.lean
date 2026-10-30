/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartIntersections

/-!
The parameter-zero and parameter-one closed subschemes on actual projective
coordinate charts are categorical pullbacks along the chart scalar maps.
This does not yet construct the global projective ideal-sheaf family or
identify the ambient Proj base change over Spec K[T].
-/

@[expose] public section

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {K ι : Type u} [Field K]

noncomputable def homogeneousParameterChartIdealSheaf
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    (polynomialProjectiveCoordinateChart n (Polynomial K) k).IdealSheafData :=
  projectiveChartIdealSheaf (Polynomial K) k
    (homogeneousParameterChartLocalizationIdeal I w p f d hf k)

theorem homogeneousParameterChartIdealSheaf_at_zero
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    (homogeneousParameterChartIdealSheaf I w p f d hf k).comap
        (projectiveChartScalarSchemeMap (Polynomial.evalRingHom 0) k) =
      projectiveChartIdealSheaf K k (projectiveChartMonomialIdeal (R := K) I p k) := by
  rw [homogeneousParameterChartIdealSheaf, projectiveChartIdealSheaf_scalar,
    homogeneousParameterChartLocalizationIdeal_at_zero I w p f d hf k hp hw]

theorem homogeneousParameterChartIdealSheaf_at_one
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    (homogeneousParameterChartIdealSheaf I w p f d hf k).comap
        (projectiveChartScalarSchemeMap (Polynomial.evalRingHom 1) k) =
      projectiveChartIdealSheaf K k (homogeneousChartLocalizationIdeal I f d hf k) := by
  rw [homogeneousParameterChartIdealSheaf, projectiveChartIdealSheaf_scalar,
    homogeneousParameterChartLocalizationIdeal_at_one]

theorem homogeneousParameterChartZeroSubscheme_pullback
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    ∃ e : (projectiveChartIdealSheaf K k (projectiveChartMonomialIdeal (R := K) I p k)).subscheme ≅
      pullback (projectiveChartScalarSchemeMap (Polynomial.evalRingHom 0) k)
        (homogeneousParameterChartIdealSheaf I w p f d hf k).subschemeι,
      e.hom ≫ pullback.fst _ _ =
        (projectiveChartIdealSheaf K k (projectiveChartMonomialIdeal (R := K) I p k)).subschemeι := by
  rw [← homogeneousParameterChartIdealSheaf_at_zero I w p f d hf k hp hw]
  exact ⟨(homogeneousParameterChartIdealSheaf I w p f d hf k).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

theorem homogeneousParameterChartOneSubscheme_pullback
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    ∃ e : (projectiveChartIdealSheaf K k (homogeneousChartLocalizationIdeal I f d hf k)).subscheme ≅
      pullback (projectiveChartScalarSchemeMap (Polynomial.evalRingHom 1) k)
        (homogeneousParameterChartIdealSheaf I w p f d hf k).subschemeι,
      e.hom ≫ pullback.fst _ _ =
        (projectiveChartIdealSheaf K k (homogeneousChartLocalizationIdeal I f d hf k)).subschemeι := by
  rw [← homogeneousParameterChartIdealSheaf_at_one I w p f d hf k]
  exact ⟨(homogeneousParameterChartIdealSheaf I w p f d hf k).comapIso _,
    Scheme.IdealSheafData.comapIso_hom_fst _ _⟩

theorem projectiveChartIdealSheaf_top (R : Type u) [CommRing R] (k : Fin n) :
    projectiveChartIdealSheaf R k ⊤ = ⊤ := by
  have h : specIdealSheaf (⊤ : Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) R) (MvPolynomial.X k))) = ⊤ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp [specIdealSheaf, Ideal.map_top]
  rw [projectiveChartIdealSheaf, h, Scheme.IdealSheafData.comap_top]

theorem projectiveChartMonomialSubscheme_isEmpty
    (I : Finset ι) (p : ι → Fin n →₀ ℕ) (k : Fin n) (l : I) (d : ℕ)
    (hl : p l = Finsupp.single k d) :
    IsEmpty (projectiveChartIdealSheaf K k
      (projectiveChartMonomialIdeal (R := K) I p k)).subscheme := by
  rw [projectiveChartMonomialIdeal_eq_top I p k l d hl, projectiveChartIdealSheaf_top]
  infer_instance

end MixedFujita
