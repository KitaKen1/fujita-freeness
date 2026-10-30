/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartAlgebra
public import MixedFujita.HomogeneousIdealFamily

/-!
Actual affine chart ideals of the homogeneous parameter family. Scalar
evaluation, including the monomial special fiber, commutes with chart
dehomogenization. The actual homogeneous-localization generators f/X_k^d
map to these affine generators, preserving the generated ideal rather than
only its radical. The ring isomorphism is supplied by ProjectiveChartEquiv.
Relative ideal-sheaf gluing and lct formulas remain separate.
-/

@[expose] public section

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {K ι : Type*} [Field K]

noncomputable def projectiveChartIdeal {R : Type*} [CommRing R] (k : Fin n)
    (J : Ideal (MvPolynomial (Fin n) R)) : Ideal (MvPolynomial {j : Fin n // j ≠ k} R) :=
  Ideal.map (projectiveDehomogenize R k) J

theorem projectiveChartIdeal_scalar_baseChange {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) (J : Ideal (MvPolynomial (Fin n) R)) :
    Ideal.map (MvPolynomial.map c) (projectiveChartIdeal k J) =
      projectiveChartIdeal k (Ideal.map (MvPolynomial.map c) J) := by
  unfold projectiveChartIdeal
  rw [Ideal.map_map, Ideal.map_map]
  apply congrArg (fun g => Ideal.map g J)
  apply RingHom.ext
  intro f
  exact projectiveDehomogenize_scalar_commutes c k f

noncomputable def homogeneousParameterChartIdeal (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n) :
    Ideal (MvPolynomial {j : Fin n // j ≠ k} (Polynomial K)) :=
  projectiveChartIdeal k (homogeneousParameterIdeal I w p f)

theorem homogeneousParameterChartIdeal_generators (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n) :
    homogeneousParameterChartIdeal I w p f k =
      Ideal.span (Set.range (fun l : I => projectiveDehomogenize (Polynomial K) k
        (homogeneousParameterFamily w (p l) (f l)))) := by
  rw [homogeneousParameterChartIdeal, projectiveChartIdeal, homogeneousParameterIdeal,
    Ideal.map_span, ← Set.range_comp']

theorem homogeneousParameterChartIdeal_at_one (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n) :
    Ideal.map (MvPolynomial.map (Polynomial.evalRingHom 1))
      (homogeneousParameterChartIdeal I w p f k) =
        projectiveChartIdeal k (Ideal.span (Set.range (fun l : I => f l))) := by
  rw [homogeneousParameterChartIdeal, projectiveChartIdeal_scalar_baseChange,
    homogeneousParameterIdeal_at_one]

theorem homogeneousParameterChartIdeal_at_zero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q) :
    Ideal.map (MvPolynomial.map (Polynomial.evalRingHom 0))
      (homogeneousParameterChartIdeal I w p f k) =
        Ideal.span (Set.range (fun l : I =>
          (p l).prod (fun i e => projectiveChartVariable K k i ^ e))) := by
  rw [homogeneousParameterChartIdeal, projectiveChartIdeal_scalar_baseChange,
    homogeneousParameterIdeal_at_zero I w p f hp hw, projectiveChartIdeal,
    Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  rw [projectiveDehomogenize_monomial, map_one, one_mul]

theorem homogeneousParameterChartIdeal_nonzero (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n)
    {t : K} (ht : t ≠ 0)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q) :
    Ideal.map (MvPolynomial.map (Polynomial.evalRingHom t))
      (homogeneousParameterChartIdeal I w p f k) =
        projectiveChartIdeal k
          (Ideal.map (polynomialDiagonalHom w t) (Ideal.span (Set.range (fun l : I => f l)))) := by
  rw [homogeneousParameterChartIdeal, projectiveChartIdeal_scalar_baseChange,
    homogeneousParameterIdeal_nonzero_fiber I w p f ht hw]

theorem homogeneousParameterChartIdeal_unit_special_fiber (I : Finset ι) (w : Fin n → ℕ)
    (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K) (k : Fin n)
    (hp : ∀ l ∈ I, p l ∈ (f l).support)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support, q ≠ p l →
      polynomialExponentWeight w (p l) < polynomialExponentWeight w q)
    (l : I) (d : ℕ) (hl : p l = Finsupp.single k d) :
    Ideal.map (MvPolynomial.map (Polynomial.evalRingHom 0))
      (homogeneousParameterChartIdeal I w p f k) = ⊤ := by
  rw [homogeneousParameterChartIdeal_at_zero I w p f k hp hw]
  apply (Ideal.eq_top_iff_one _).mpr
  have hmem := Ideal.subset_span (Set.mem_range_self
    (f := fun l : I => (p l).prod (fun i e => projectiveChartVariable K k i ^ e)) l)
  have heq : (p l).prod (fun i e => projectiveChartVariable K k i ^ e) = 1 := by
    rw [hl]
    simp [projectiveChartVariable]
  rwa [heq] at hmem

noncomputable def homogeneousParameterChartLocalizationIdeal (I : Finset ι)
    (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K)
    (d : ℕ) (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin n) (Polynomial K)) (MvPolynomial.X k)) :=
  Ideal.span (Set.range (fun l : I => HomogeneousLocalization.Away.mk _
    (MvPolynomial.isHomogeneous_X (Polynomial K) k) d
    (homogeneousParameterFamily w (p l) (f l))
    (by simpa using homogeneousParameterFamily_isHomogeneous w (p l) (hf l l.property))))

theorem homogeneousParameterChartLocalizationIdeal_affine (I : Finset ι)
    (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ) (f : ι → MvPolynomial (Fin n) K)
    (d : ℕ) (hf : ∀ l ∈ I, (f l).IsHomogeneous d) (k : Fin n) :
    Ideal.map (projectiveChartLocalizationToAffine (Polynomial K) k)
      (homogeneousParameterChartLocalizationIdeal I w p f d hf k) =
        homogeneousParameterChartIdeal I w p f k := by
  rw [homogeneousParameterChartLocalizationIdeal, Ideal.map_span, ← Set.range_comp',
    homogeneousParameterChartIdeal_generators]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext l
  exact projectiveChartLocalizationToAffine_mk (Polynomial K) k d _
    (homogeneousParameterFamily_isHomogeneous w (p l) (hf l l.property))

end MixedFujita
