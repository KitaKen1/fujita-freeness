/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierBirationalZeroDivisors
public import MixedFujita.RegularFunctionGluing

/-!
Actual Cartier sections along an arbitrary integral Stein-type morphism. Surjectivity of the
maps on regular functions on all opens, together with dominance, suffices: no surjectivity of
the function-field map, birationality, normality or noetherianity is assumed. A section upstairs
has a regular coefficient on one pulled-back trivializing open; descend that coefficient to
show its rational function comes from downstairs. Pointwise regularity of the descended section
then follows by the same argument on every trivializing open. This identifies every graded
Cartier section space, including on the positive-dimensional fibres of an actual Stein map.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (g : T ⟶ X) [IsDominant g]
  (happ : ∀ U : X.Opens, Function.Surjective (g.app U).hom)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

include happ

/-- Regularity of a rational function is reflected on an entire nonempty open by the actual
surjective open-section map. -/
theorem stein_exists_regular_function_of_pullback_regular (U : X.Opens) [Nonempty U]
    (r : X.functionField)
    (hreg : ∀ t ∈ g ⁻¹ᵁ U, (dominantFunctionFieldMap g).hom r ∈
      (algebraMap (T.presheaf.stalk t) T.functionField).range) :
    ∃ a : Γ(X, U), X.germToFunctionField U a = r := by
  have := dominant_preimage_nonempty g U
  obtain ⟨b, hb⟩ := exists_section_of_forall_mem_stalk_range (g ⁻¹ᵁ U)
    ((dominantFunctionFieldMap g).hom r) hreg
  obtain ⟨a, ha⟩ := happ U b
  refine ⟨a, (dominantFunctionFieldMap g).hom.injective ?_⟩
  rw [dominantFunctionFieldMap_germ g U (g ⁻¹ᵁ U) le_rfl,
    Scheme.Hom.appLE_eq_app, ha, hb]

/-- A rational section regular after Stein-type pullback was already regular downstairs. -/
theorem mem_sections_of_cartierPullback_of_open_app_surjective
    (D : CartierDivisor X) (r : X.functionField)
    (hs : (rationalFunctionsEquiv (X := T) ⊤).symm ((dominantFunctionFieldMap g).hom r) ∈
      (cartierPullback g D).sections ⊤) :
    (rationalFunctionsEquiv (X := X) ⊤).symm r ∈ D.sections ⊤ := by
  rw [CartierDivisor.mem_sections]
  intro x _ f hf
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨U, hx, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have : Nonempty U := ⟨⟨x, hx⟩⟩
  obtain ⟨a, ha⟩ := stein_exists_regular_function_of_pullback_regular g happ U
    ((f : X.functionField) * r) (fun t ht => by
      have hft := cartierPullback_isLocalEquationAt g D t
        (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hU ht)
      have h := (CartierDivisor.mem_sections.mp hs) t (Opens.mem_top _) _ hft
      rw [LinearEquiv.apply_symm_apply] at h
      change (dominantFunctionFieldMap g).hom (f : X.functionField) *
        (dominantFunctionFieldMap g).hom r ∈ _ at h
      rwa [map_mul])
  refine ⟨X.presheaf.germ U x hx a, ?_⟩
  rw [X.algebraMap_germ_eq_germToFunctionField hx, ha]

/-- Every actual section of a Cartier pullback has a rational function in the image of the
function field downstairs, even though that function-field map need not be surjective. -/
theorem stein_cartier_section_rational_in_image (D : CartierDivisor X)
    (s : Γ((cartierPullback g D).sheaf, ⊤)) :
    ∃ r : X.functionField, (dominantFunctionFieldMap g).hom r =
      cartierSectionRational (cartierPullback g D) s := by
  let U := cartierChosenOpen D (genericPoint X)
  let f := cartierChosenEquation D (genericPoint X)
  have := dominant_preimage_nonempty g U
  have hreg (t : T) (ht : t ∈ g ⁻¹ᵁ U) :
      ((dominantFunctionFieldMap g).hom (f : X.functionField)) *
          cartierSectionRational (cartierPullback g D) s ∈
        (algebraMap (T.presheaf.stalk t) T.functionField).range := by
    have hf := cartierPullback_isLocalEquationAt g D t
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
        (cartierChosenOpen_spec D (genericPoint X)) ht)
    exact ⟨cartierLocalCoefficient _ t _ hf s, cartierLocalCoefficient_image _ t _ hf s⟩
  obtain ⟨b, hb⟩ := exists_section_of_forall_mem_stalk_range (g ⁻¹ᵁ U) _ hreg
  obtain ⟨a, ha⟩ := happ U b
  have ha' : (dominantFunctionFieldMap g).hom (X.germToFunctionField U a) =
      (dominantFunctionFieldMap g).hom (f : X.functionField) *
        cartierSectionRational (cartierPullback g D) s := by
    rw [dominantFunctionFieldMap_germ g U (g ⁻¹ᵁ U) le_rfl,
      Scheme.Hom.appLE_eq_app, ha, hb]
  refine ⟨X.germToFunctionField U a / (f : X.functionField), ?_⟩
  rw [map_div₀, ha']
  exact mul_div_cancel_left₀ _ ((map_ne_zero_iff _ (dominantFunctionFieldMap g).hom.injective).mpr (Units.ne_zero f))

/-- The actual pullback map on Cartier global sections is surjective for a Stein-type map. -/
theorem cartierDominantPullbackSection_surjective_of_open_app_surjective
    (D : CartierDivisor X) : Function.Surjective (cartierDominantPullbackSection g D) := by
  intro s
  obtain ⟨r, hr⟩ := stein_cartier_section_rational_in_image g happ D s
  have hm : (rationalFunctionsEquiv (X := T) ⊤).symm ((dominantFunctionFieldMap g).hom r) ∈
      (cartierPullback g D).sections ⊤ := by
    rw [hr, cartierSectionRational_apply, LinearEquiv.symm_apply_apply]
    exact (cartierPullback g D).sheafι_app_mem ⊤ s
  have hreg := mem_sections_of_cartierPullback_of_open_app_surjective g happ D r hm
  refine ⟨CartierDivisor.sectionMk _ hreg, ?_⟩
  apply cartierSectionRational_injective _
  rw [cartierDominantPullbackSection_rational, cartierSectionRational_sectionMk, hr]

section BaseField

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))] [g.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra functionFieldBaseAlgebra
  cartierBaseSectionScalarTower functionFieldBaseScalarTower

/-- All actual section subspaces, rather than only the sections of a chosen finite system,
are identified by the function-field embedding along a Stein-type map. -/
theorem stein_cartierSectionSpace_pullback (D : CartierDivisor X) :
    cartierSectionSpace K (cartierPullback g D) =
      (cartierSectionSpace K D).map (dominantFunctionFieldAlgHom (K := K) g).toLinearMap := by
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := cartierDominantPullbackSection_surjective_of_open_app_surjective g happ D s
    exact ⟨cartierSectionRational D t, ⟨t, rfl⟩, (cartierDominantPullbackSection_rational g D t).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact (mem_cartierSectionSpace_iff _ _).mpr
      (cartierPullback_mem_sections g D r ((mem_cartierSectionSpace_iff D r).mp hr))

/-- Stein-type pullback preserves the dimension of the full actual space of global sections. -/
theorem stein_finrank_sections_cartierPullback (D : CartierDivisor X) :
    Module.finrank K Γ((cartierPullback g D).sheaf, ⊤) = Module.finrank K Γ(D.sheaf, ⊤) := by
  rw [← finrank_cartierSectionSpace K, ← finrank_cartierSectionSpace K,
    stein_cartierSectionSpace_pullback g happ K D]
  exact (Submodule.equivMapOfInjective _
    (dominantFunctionFieldAlgHom (K := K) g).toRingHom.injective _).finrank_eq.symm

/-- The comparison uses one fixed Stein target at every degree. -/
theorem stein_finrank_sections_nsmul_cartierPullback (D : CartierDivisor X) (q : ℕ) :
    Module.finrank K Γ((q • cartierPullback g D).sheaf, ⊤) =
      Module.finrank K Γ((q • D).sheaf, ⊤) := by
  rw [← cartierPullback_nsmul]
  exact stein_finrank_sections_cartierPullback g happ K (q • D)

end BaseField

end MixedFujita
