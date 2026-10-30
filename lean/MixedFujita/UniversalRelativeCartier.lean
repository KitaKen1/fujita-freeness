/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveRelativeCartier
public import MixedFujita.UniversalHomogeneousForm

/-!
The previously constructed universal linear combinations now have actual
relative-Cartier presentations on their nonzero coefficient locus. The
coefficient-parameter rings over a domain, and over K[T], are domains. A
single included nonzero generator proves that the universal equation is
nonzero. For the T-family this follows already by specialization at one;
no strict initial-weight inequality is needed for this global nonvanishing.

The presentations use actual module sheaves, inclusions, ideal images and
proved flatness. They do not supply Bertini, ideal/divisor lct comparison,
lct semicontinuity, or arbitrary-base-change preservation of the presentation.
-/

@[expose] public section

namespace MixedFujita

universe u

variable {n : ℕ} {ι : Type u}

noncomputable def universalHomogeneousRelativeCartierPresentation
    (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (I : Finset ι) (g : ι → MvPolynomial (Fin n) R) (d : ℕ)
    (hg : ∀ l ∈ I, (g l).IsHomogeneous d) {l : ι} (hl : l ∈ I) (h0 : g l ≠ 0) :
    RelativeCartierPresentation (projectiveNonzeroAmbientProjection (universalHomogeneousForm I g))
      (projectiveNonzeroAmbientHypersurfaceIdeal (universalHomogeneousForm I g) d
        (universalHomogeneousForm_isHomogeneous I g d hg)) :=
  projectiveNonzeroRelativeCartierPresentation (MvPolynomial ι R) k₀ d
    (universalHomogeneousForm I g) (universalHomogeneousForm_isHomogeneous I g d hg)
    (universalHomogeneousForm_ne_zero I g hl h0)

variable {K : Type u} [Field K]

theorem universalParameterHomogeneousForm_ne_zero
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) {l : ι} (hl : l ∈ I) (h0 : f l ≠ 0) :
    universalParameterHomogeneousForm I w p f ≠ 0 := by
  intro h
  have h1 := universalParameterHomogeneousForm_at_one I w p f
  rw [h, map_zero] at h1
  exact universalHomogeneousForm_ne_zero I f hl h0 h1.symm

noncomputable def universalParameterRelativeCartierPresentation
    (k₀ : Fin n) (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (d : ℕ)
    (hf : ∀ l ∈ I, (f l).IsHomogeneous d) {l : ι} (hl : l ∈ I) (h0 : f l ≠ 0) :
    RelativeCartierPresentation
      (projectiveNonzeroAmbientProjection (universalParameterHomogeneousForm I w p f))
      (projectiveNonzeroAmbientHypersurfaceIdeal (universalParameterHomogeneousForm I w p f) d
        (universalParameterHomogeneousForm_isHomogeneous I w p f d hf)) :=
  projectiveNonzeroRelativeCartierPresentation (MvPolynomial ι (Polynomial K)) k₀ d
    (universalParameterHomogeneousForm I w p f)
    (universalParameterHomogeneousForm_isHomogeneous I w p f d hf)
    (universalParameterHomogeneousForm_ne_zero I w p f hl h0)

end MixedFujita
