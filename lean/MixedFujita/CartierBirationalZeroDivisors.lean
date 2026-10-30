/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperBirationalSections
public import MixedFujita.CartierGlobalGenerationFiniteFamily

/-!
Actual global Cartier sections pull back under a dominant map. Their rational
functions and effective zero divisors agree with the actual pullbacks. On a
normal source every section on a proper birational pullback descends, with its
actual zero divisor. This connects Bertini sections to source perturbations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (ρ : T ⟶ X) [IsDominant ρ]

attribute [local instance] cartierGlobalStalkAlgebra

/-- Construct the actual pulled-back section using its regular rational function. -/
noncomputable def cartierDominantPullbackSection (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) : Γ((cartierPullback ρ D).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (cartierPullback_mem_sections ρ D (cartierSectionRational D s)
    (by
      rw [cartierSectionRational_apply, LinearEquiv.symm_apply_apply]
      exact D.sheafι_app_mem ⊤ s))

/-- The constructed section has exactly the actual pulled rational function. -/
theorem cartierDominantPullbackSection_rational (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionRational (cartierPullback ρ D) (cartierDominantPullbackSection ρ D s) =
      (dominantFunctionFieldMap ρ).hom (cartierSectionRational D s) :=
  cartierSectionRational_sectionMk _ _ _

/-- Pullback preserves nonzero actual global sections. -/
theorem cartierDominantPullbackSection_ne_zero (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : cartierDominantPullbackSection ρ D s ≠ 0 := by
  intro h
  apply hs
  apply cartierSectionRational_injective D
  apply (dominantFunctionFieldMap ρ).hom.injective
  rw [map_zero, map_zero, ← cartierDominantPullbackSection_rational, h, map_zero]

/-- Units representing actual nonzero sections agree under actual pullback. -/
theorem cartierDominantPullbackSection_unit (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionUnit (cartierPullback ρ D) (cartierDominantPullbackSection ρ D s)
      (cartierDominantPullbackSection_ne_zero ρ D s hs) =
        Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom (cartierSectionUnit D s hs) := by
  apply Units.ext
  simp only [cartierSectionUnit_val, Units.coe_map, cartierDominantPullbackSection_rational]
  rfl

/-- The effective zero divisor of the actual pulled section is the actual Cartier pullback. -/
theorem cartierDominantPullbackSection_zeroDivisor (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionZeroDivisor (cartierPullback ρ D) (cartierDominantPullbackSection ρ D s)
      (cartierDominantPullbackSection_ne_zero ρ D s hs) =
        cartierPullback ρ (cartierSectionZeroDivisor D s hs) := by
  unfold cartierSectionZeroDivisor
  rw [cartierPullback_add, cartierPullback_principal, cartierDominantPullbackSection_unit]

/-- Actual regular local coefficients commute with the actual stalk pullback. -/
theorem cartierDominantPullbackSection_localCoefficient (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : T) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt (ρ t) f) :
    cartierLocalCoefficient (cartierPullback ρ D) t
      (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f)
      (cartierPullback_isLocalEquationAt ρ D t hf) (cartierDominantPullbackSection ρ D s) =
        ρ.stalkMap t (cartierLocalCoefficient D (ρ t) f hf s) := by
  apply IsFractionRing.injective (T.presheaf.stalk t) T.functionField
  rw [cartierLocalCoefficient_image, cartierDominantPullbackSection_rational,
    ← dominantFunctionFieldMap_algebraMap, cartierLocalCoefficient_image, map_mul]
  rfl

/-- Ordinary global generation pulls back under any actual dominant morphism. -/
theorem cartierIsGloballyGenerated_cartierPullback (D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) : CartierIsGloballyGenerated (cartierPullback ρ D) := by
  intro t
  obtain ⟨s, hs⟩ := hD (ρ t)
  let f := Classical.choose (D.exists_isLocalEquationAt (ρ t))
  have hf : D.IsLocalEquationAt (ρ t) f := Classical.choose_spec (D.exists_isLocalEquationAt (ρ t))
  let g := Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f
  have hg := cartierPullback_isLocalEquationAt ρ D t hf
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (cartierPullback ρ D) t
    (Classical.choose ((cartierPullback ρ D).exists_isLocalEquationAt t)) g
    (Classical.choose_spec ((cartierPullback ρ D).exists_isLocalEquationAt t)) hg
  refine ⟨cartierDominantPullbackSection ρ D s, ?_⟩
  rw [hv, cartierDominantPullbackSection_localCoefficient ρ D s t f hf]
  exact v.isUnit.mul (hs.map (ρ.stalkMap t).hom)

variable [IsLocallyNoetherian X] [IsProper ρ]

/-- Proper birational pullbacks to a normal source have no additional actual global sections. -/
theorem cartierDominantPullbackSection_surjective
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (D : CartierDivisor X) :
    Function.Surjective (cartierDominantPullbackSection ρ D) := by
  intro s
  obtain ⟨g, hg⟩ := hρ (cartierSectionRational (cartierPullback ρ D) s)
  have hm : (rationalFunctionsEquiv (X := T) ⊤).symm
      ((dominantFunctionFieldMap ρ).hom g) ∈ (cartierPullback ρ D).sections ⊤ := by
    rw [hg, cartierSectionRational_apply, LinearEquiv.symm_apply_apply]
    exact (cartierPullback ρ D).sheafι_app_mem ⊤ s
  have hreg := mem_sections_of_cartierPullback ρ hnorm
    (fun ξ _ => surjective_of_isProper_of_isDominant ρ ξ) D g hm
  refine ⟨CartierDivisor.sectionMk _ hreg, ?_⟩
  apply cartierSectionRational_injective (cartierPullback ρ D)
  rw [cartierDominantPullbackSection_rational, cartierSectionRational_sectionMk, hg]

/-- Every nonzero section on a proper birational pullback descends together with its zero divisor. -/
theorem proper_birational_exists_section_zeroDivisor_descent
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom) (D : CartierDivisor X)
    (s : Γ((cartierPullback ρ D).sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ (t : Γ(D.sheaf, ⊤)) (ht : t ≠ 0),
      cartierDominantPullbackSection ρ D t = s ∧
      cartierPullback ρ (cartierSectionZeroDivisor D t ht) =
        cartierSectionZeroDivisor (cartierPullback ρ D) s hs := by
  obtain ⟨t, ht⟩ := cartierDominantPullbackSection_surjective ρ hnorm hρ D s
  have ht0 : t ≠ 0 := by
    intro h0
    apply hs
    apply cartierSectionRational_injective (cartierPullback ρ D)
    rw [← ht, cartierDominantPullbackSection_rational, h0, map_zero, map_zero, map_zero]
  refine ⟨t, ht0, ht, ?_⟩
  rw [← cartierDominantPullbackSection_zeroDivisor ρ D t ht0]
  simp only [ht]

end MixedFujita
