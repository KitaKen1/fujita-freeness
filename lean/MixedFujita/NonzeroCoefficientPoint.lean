/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveRelativeCartier

/-!
Actual coefficient-Spec morphisms into the nonzero coefficient open.
A unit coefficient makes that open the whole spectrum; in particular this
holds for every nonzero polynomial over a field. Open-immersion lifting gives
the factor morphism and its actual pullback square, rather than just a point
membership assertion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

noncomputable def schemeOpenFactor {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    (h : g ⁻¹ᵁ U = ⊤) : X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι g (by
    rw [Scheme.Opens.range_ι, Set.range_subset_iff]
    intro x
    have hx : x ∈ g ⁻¹ᵁ U := by rw [h]; trivial
    exact hx)

@[reassoc (attr := simp)]
theorem schemeOpenFactor_ι {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    (h : g ⁻¹ᵁ U = ⊤) : schemeOpenFactor g U h ≫ U.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

theorem schemeOpenFactor_isPullback {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.Opens)
    (h : g ⁻¹ᵁ U = ⊤) : IsPullback (schemeOpenFactor g U h) (𝟙 X) U.ι g :=
  IsOpenImmersion.isPullback_lift_id _ _ _

theorem polynomialNonzeroLocus_eq_top_of_unit_coefficient
    {R σ : Type*} [CommRing R] (f : MvPolynomial σ R) (q : σ →₀ ℕ)
    (hq : IsUnit (f.coeff q)) : polynomialNonzeroLocus f = ⊤ := by
  apply top_unique
  intro p _
  change ¬ polynomialCoefficientIdeal f ≤ p.asIdeal
  intro h
  exact p.isPrime.ne_top (p.asIdeal.eq_top_of_isUnit_mem
    ((polynomialCoefficientIdeal_le_iff f p.asIdeal).mp h q) hq)

theorem polynomial_field_nonzero_has_unit_coefficient
    {K σ : Type*} [Field K] (f : MvPolynomial σ K) (h0 : f ≠ 0) :
    ∃ q, IsUnit (f.coeff q) := by
  have h : ∃ q, f.coeff q ≠ 0 := by
    by_contra! h
    apply h0
    ext q
    simpa using h q
  obtain ⟨q, hq⟩ := h
  exact ⟨q, isUnit_iff_ne_zero.mpr hq⟩

theorem polynomialNonzeroLocus_eq_top_of_field_nonzero
    {K σ : Type*} [Field K] (f : MvPolynomial σ K) (h0 : f ≠ 0) :
    polynomialNonzeroLocus f = ⊤ := by
  obtain ⟨q, hq⟩ := polynomial_field_nonzero_has_unit_coefficient f h0
  exact polynomialNonzeroLocus_eq_top_of_unit_coefficient f q hq

theorem polynomialNonzeroLocus_spec_preimage {R S : Type u} {σ : Type*}
    [CommRing R] [CommRing S] (c : R →+* S) (f : MvPolynomial σ R) :
    (Spec.map (CommRingCat.ofHom c)) ⁻¹ᵁ
        (polynomialNonzeroLocus f : (Spec (CommRingCat.of R)).Opens) =
      (polynomialNonzeroLocus (MvPolynomial.map c f) : (Spec (CommRingCat.of S)).Opens) :=
  Opens.ext (polynomialNonzeroLocus_baseChange c f)

noncomputable def coefficientNonzeroPoint {R S : Type u} {σ : Type*}
    [CommRing R] [CommRing S] (c : R →+* S) (f : MvPolynomial σ R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    Spec (CommRingCat.of S) ⟶
      Scheme.Opens.toScheme (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f) :=
  schemeOpenFactor (Spec.map (CommRingCat.ofHom c)) _
    ((polynomialNonzeroLocus_spec_preimage c f).trans h)

@[reassoc (attr := simp)]
theorem coefficientNonzeroPoint_ι {R S : Type u} {σ : Type*}
    [CommRing R] [CommRing S] (c : R →+* S) (f : MvPolynomial σ R)
    (h : polynomialNonzeroLocus (MvPolynomial.map c f) = ⊤) :
    coefficientNonzeroPoint c f h ≫
      (Scheme.Opens.ι (X := Spec (CommRingCat.of R)) (polynomialNonzeroLocus f)) =
        Spec.map (CommRingCat.ofHom c) :=
  schemeOpenFactor_ι _ _ _

end MixedFujita
