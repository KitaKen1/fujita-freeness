/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedCoefficientCartierFamily

/-!
Select a nonzero K-valued parameter in the nonzero-form open using actual
properness of its restricted projective ambient. The closed bad locus may
be defined only on that ambient open; closedness on the entire projective
K[T]-Scheme is not required. Its closedness and zero-fiber avoidance remain
explicit hypotheses. In particular no lct semicontinuity or Bertini theorem
is hidden in this specialization result.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

theorem properScheme_good_neighborhood {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    {Z : Set X} (hZ : IsClosed Z) (y : Y)
    (hy : ∀ x, g x = y → x ∉ Z) :
    ∃ U : Y.Opens, y ∈ U ∧ ∀ x, g x ∈ U → x ∉ Z := by
  let U : Y.Opens := ⟨(g '' Z)ᶜ, (Scheme.Hom.isClosedMap g Z hZ).isOpen_compl⟩
  refine ⟨U, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hy x hxy hx
  · intro x hx hxZ
    exact hx ⟨x, hxZ, rfl⟩

theorem projectiveNonzeroAmbientProjection_isProper
    {n : ℕ} {R : Type u} [CommRing R] (f : MvPolynomial (Fin n) R) :
    IsProper (projectiveNonzeroAmbientProjection f) :=
  IsZariskiLocalAtTarget.restrict (P := @IsProper)
    (polynomialProjectiveToBase_isProper n R) (polynomialNonzeroLocus f)

variable {n : ℕ} {K ι : Type u} [Field K]

theorem projectiveNonzeroForm_good_nonzero_parameter [Infinite K]
    (F : MvPolynomial (Fin n) (Polynomial K))
    (hzero : MvPolynomial.map (Polynomial.evalRingHom 0) F ≠ 0)
    {Z : Set (((polynomialProjectiveToBase n (Polynomial K)) ⁻¹ᵁ
      (polynomialNonzeroLocus F : (Spec (CommRingCat.of (Polynomial K))).Opens)).toScheme)}
    (hZ : IsClosed Z)
    (hgoodzero : ∀ x, projectiveNonzeroAmbientProjection F x =
      (⟨polynomialParameterPoint (0 : K),
        (polynomialParameterPoint_mem_nonzeroLocus 0 F).mpr hzero⟩ :
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
          (polynomialNonzeroLocus F)) →
      x ∉ Z) :
    ∃ t : K, t ≠ 0 ∧ ∃ hF : MvPolynomial.map (Polynomial.evalRingHom t) F ≠ 0,
      ∀ x, projectiveNonzeroAmbientProjection F x =
        (⟨polynomialParameterPoint t,
          (polynomialParameterPoint_mem_nonzeroLocus t F).mpr hF⟩ :
          Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
            (polynomialNonzeroLocus F)) →
        x ∉ Z := by
  let B : (Spec (CommRingCat.of (Polynomial K))).Opens := polynomialNonzeroLocus F
  let y0 : B.toScheme := ⟨polynomialParameterPoint 0,
    (polynomialParameterPoint_mem_nonzeroLocus 0 F).mpr hzero⟩
  let _ := projectiveNonzeroAmbientProjection_isProper F
  obtain ⟨U, hU, hgood⟩ := properScheme_good_neighborhood
    (projectiveNonzeroAmbientProjection F) hZ y0 hgoodzero
  obtain ⟨t, ht, hV⟩ := polynomialParameterPoint_mem_open_nonzero (B.ι ''ᵁ U) 0
    ⟨y0, hU, rfl⟩
  obtain ⟨y, hy, he⟩ := hV
  change y.1 = polynomialParameterPoint t at he
  have hB : polynomialParameterPoint t ∈ B := he ▸ y.property
  have hF := (polynomialParameterPoint_mem_nonzeroLocus t F).mp hB
  refine ⟨t, ht, hF, ?_⟩
  intro x hx
  apply hgood x
  rw [hx]
  have he' : y = (⟨polynomialParameterPoint t,
      (polynomialParameterPoint_mem_nonzeroLocus t F).mpr hF⟩ : B.toScheme) :=
    Subtype.ext he
  exact he' ▸ hy

theorem fixedCoefficient_good_original_combination [Infinite K]
    (I : Finset ι) (w : Fin n → ℕ) (p : ι → Fin n →₀ ℕ)
    (f : ι → MvPolynomial (Fin n) K) (a : ι → K)
    (hw : ∀ l ∈ I, ∀ q ∈ (f l).support,
      polynomialExponentWeight w (p l) ≤ polynomialExponentWeight w q)
    (hzero : MvPolynomial.map (Polynomial.evalRingHom 0)
      (fixedCoefficientParameterForm I w p f a) ≠ 0)
    {Z : Set (((polynomialProjectiveToBase n (Polynomial K)) ⁻¹ᵁ
      (polynomialNonzeroLocus (fixedCoefficientParameterForm I w p f a) :
        (Spec (CommRingCat.of (Polynomial K))).Opens)).toScheme)}
    (hZ : IsClosed Z)
    (hgoodzero : ∀ x, projectiveNonzeroAmbientProjection (fixedCoefficientParameterForm I w p f a) x =
      (⟨polynomialParameterPoint (0 : K),
        (polynomialParameterPoint_mem_nonzeroLocus 0 _).mpr hzero⟩ :
        Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
          (polynomialNonzeroLocus (fixedCoefficientParameterForm I w p f a))) → x ∉ Z) :
    ∃ t : K, t ≠ 0 ∧ ∃ hF : MvPolynomial.map (Polynomial.evalRingHom t)
        (fixedCoefficientParameterForm I w p f a) ≠ 0,
      (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) ≠ 0 ∧
      (∑ l ∈ I, MvPolynomial.C (correctedCoefficientVector w p a t l) * f l) ∈
        Ideal.span (Set.range (fun l : I => f l)) ∧
      ∀ x, projectiveNonzeroAmbientProjection (fixedCoefficientParameterForm I w p f a) x =
        (⟨polynomialParameterPoint t,
          (polynomialParameterPoint_mem_nonzeroLocus t _).mpr hF⟩ :
          Scheme.Opens.toScheme (X := Spec (CommRingCat.of (Polynomial K)))
            (polynomialNonzeroLocus (fixedCoefficientParameterForm I w p f a))) → x ∉ Z := by
  obtain ⟨t, ht, hF, hgood⟩ := projectiveNonzeroForm_good_nonzero_parameter
    (fixedCoefficientParameterForm I w p f a) hzero hZ hgoodzero
  obtain ⟨h0, hmem⟩ := fixedCoefficientParameterForm_nonzero_original_combination
    I w p f a ht hw hF
  exact ⟨t, ht, hF, h0, hmem, hgood⟩

end MixedFujita
