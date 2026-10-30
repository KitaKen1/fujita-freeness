/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierWeilSectionComparison
public import MixedFujita.SNCWeilCartierMultiple
public import MixedFujita.CanonicalWeilSectionDescent

/-! Realize the same effective integral SNC Weil divisor by an actual
effective Cartier divisor, without a new denominator. Preserve the actual
rational-function inclusion when transporting unique section descent. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The same actual SNC support gives an effective Cartier realization of
an effective integer Weil divisor and the actual compatible sheaf comparison. -/
theorem exists_effective_snc_integer_weil_cartier_with_sheaf_iso
    {K : Type u} [Field K] {n : ℕ} {B : Scheme.{u}} [IsIntegral B] [IsNoetherian B]
    [B.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (B ↘ Spec (CommRingCat.of K))]
    [IsSeparated (B ↘ Spec (CommRingCat.of K))]
    [∀ β : CodimensionOnePoint B, IsDiscreteValuationRing (B.presheaf.stalk (β : B))]
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    {r : ℕ} (ξ : Fin r → B) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (R : SchemeWeilDivisor B) (hR : 0 ≤ R)
    (hsupport : ∀ β : CodimensionOnePoint B, (β : B) ∉ Set.range ξ → R β = 0) :
    ∃ C : CartierDivisor B, C.IsEffective ∧
      (∀ β : CodimensionOnePoint B, cartierCoefficient C (β : B) = R β) ∧
      ∃ e : C.sheaf ≅ SchemeWeilDivisor.sheaf R,
        e.hom ≫ SchemeWeilDivisor.sheafι R = C.sheafι := by
  obtain ⟨C, hC⟩ := exists_snc_integer_weil_cartier ξ hinj hξ hsnc R hsupport
  have hEff : C.IsEffective :=
    (normal_cartier_isEffective_iff_coefficients_nonneg hnormB C).mpr
      (fun β => by rw [hC β]; exact hR β)
  have hWeil : C.toWeilDivisor = R := by
    apply WeilDivisor.ext
    intro β
    rw [cartier_toWeilDivisor_coeff_eq_cartierCoefficient]
    exact hC β
  subst R
  exact ⟨C, hEff, hC, normalCartierWeilSheafIso hnormB C,
    normalCartierWeilSheafIso_hom_ι hnormB C⟩

/-- A sheaf comparison preserving the actual rational-function inclusion
transports the unique Weil-section representation into the unique actual
Cartier-section representation, with the same source section and field map. -/
theorem unique_weil_section_descent_iff_unique_cartier_section_descent
    {S B : Scheme.{u}} [IsIntegral S] [IsIntegral B] [IsNoetherian B]
    [∀ β : CodimensionOnePoint B, IsDiscreteValuationRing (B.presheaf.stalk (β : B))]
    (q : S ⟶ B) [IsDominant q] (E : CartierDivisor S) (R : SchemeWeilDivisor B)
    (C : CartierDivisor B) (e : C.sheaf ≅ SchemeWeilDivisor.sheaf R)
    (he : e.hom ≫ SchemeWeilDivisor.sheafι R = C.sheafι)
    (U : B.Opens) [Nonempty U] (s : Γ(E.sheaf, q ⁻¹ᵁ U)) :
    letI := dominant_preimage_nonempty q U
    (∃! t : Γ(SchemeWeilDivisor.sheaf R, U),
      (dominantFunctionFieldMap q).hom
        (rationalFunctionsEquiv (X := B) U
          (Scheme.Modules.Hom.app (SchemeWeilDivisor.sheafι R) U t)) =
      rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s)) ↔
    ∃! t : Γ(C.sheaf, U),
      (dominantFunctionFieldMap q).hom
        (rationalFunctionsEquiv (X := B) U (Scheme.Modules.Hom.app C.sheafι U t)) =
      rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app E.sheafι (q ⁻¹ᵁ U) s) := by
  letI := dominant_preimage_nonempty q U
  symm
  apply (Scheme.Modules.sectionsLinearEquiv e U).toEquiv.existsUnique_congr
  intro t
  have hι : Scheme.Modules.Hom.app (SchemeWeilDivisor.sheafι R) U
      (Scheme.Modules.Hom.app e.hom U t) = Scheme.Modules.Hom.app C.sheafι U t := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, he]
  simp only [LinearEquiv.coe_toEquiv, Scheme.Modules.sectionsLinearEquiv_apply, hι]

end MixedFujita
