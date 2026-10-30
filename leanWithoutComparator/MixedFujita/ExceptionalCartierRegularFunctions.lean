/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ExceptionalCartierSections
public import MixedFujita.RegularFunctionGluing

/-!
Every actual section of an effective exceptional Cartier divisor over a target
open comes uniquely from a regular function on that open. Composing with a
Stein-type morphism preserves this actual all-open rank-one criterion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Actual sections of the zero Cartier divisor are exactly actual regular functions. -/
theorem mem_zero_cartier_sections_iff_regular_function {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (g : X.functionField) :
    (rationalFunctionsEquiv (X := X) U).symm g ∈ (0 : CartierDivisor X).sections U ↔
      ∃ a : Γ(X, U), X.germToFunctionField U a = g := by
  constructor
  · intro hs
    apply exists_section_of_forall_mem_stalk_range U g
    intro x hx
    have h := (CartierDivisor.mem_sections.mp hs) x hx 1 (CartierDivisor.isLocalEquationAt_zero x)
    simpa only [LinearEquiv.apply_symm_apply, Units.val_one, one_mul] using h
  · rintro ⟨a, ha⟩
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    refine ⟨1, CartierDivisor.isLocalEquationAt_zero x, ?_⟩
    rw [LinearEquiv.apply_symm_apply, Units.val_one, one_mul]
    exact ⟨X.presheaf.germ U x hx a, (X.algebraMap_germ_eq_germToFunctionField hx a).trans ha⟩

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]

/-- All sections of an actual effective exceptional divisor descend uniquely to
regular functions, on every nonempty open of a normal target. -/
theorem effective_exceptional_cartier_section_regular_descent
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (π : T ⟶ X) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (E : CartierDivisor T) (hEff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0)
    (U : X.Opens) [Nonempty U] (z : T.functionField) :
    letI := dominant_preimage_nonempty π U
    (rationalFunctionsEquiv (X := T) (π ⁻¹ᵁ U)).symm z ∈ E.sections (π ⁻¹ᵁ U) ↔
      ∃! a : Γ(X, U), (dominantFunctionFieldMap π).hom (X.germToFunctionField U a) = z := by
  haveI := dominant_preimage_nonempty π U
  obtain ⟨g, rfl⟩ := hπ.2 z
  have hiff := mem_sections_effective_exceptional_cartierPullback_iff_on_open
    hnorm hnormT π hπ E hEff hE (0 : CartierDivisor X) U g
  simp only [cartierPullback_zero, zero_add] at hiff
  have hinj : Function.Injective (fun a : Γ(X, U) =>
      (dominantFunctionFieldMap π).hom (X.germToFunctionField U a)) :=
    (dominantFunctionFieldMap π).hom.injective.comp (X.germToFunctionField_injective U)
  constructor
  · intro hs
    obtain ⟨a, ha⟩ := (mem_zero_cartier_sections_iff_regular_function U g).mp (hiff.mp hs)
    have heq := congrArg (dominantFunctionFieldMap π).hom ha
    exact ⟨a, heq, fun b hb => hinj (hb.trans heq.symm)⟩
  · rintro ⟨a, ha, -⟩
    exact hiff.mpr ((mem_zero_cartier_sections_iff_regular_function U g).mpr
      ⟨a, (dominantFunctionFieldMap π).hom.injective ha⟩)

/-- For a birational resolution followed by a Stein-type morphism, all actual
sections of an effective exceptional divisor come uniquely from the final base. -/
theorem effective_exceptional_stein_composite_section_descent
    {Y : Scheme.{u}} [IsIntegral Y]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (π : T ⟶ X) [IsDominant π] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldMap π).hom)
    (E : CartierDivisor T) (hEff : E.IsEffective)
    (hE : ∀ t : CodimensionOnePoint T, Order.coheight (π (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0)
    (f : X ⟶ Y) [IsDominant f]
    (happ : ∀ V : Y.Opens, Function.Surjective (f.app V).hom)
    (V : Y.Opens) [Nonempty V] (z : T.functionField) :
    letI := dominant_preimage_nonempty f V
    letI := dominant_preimage_nonempty π (f ⁻¹ᵁ V)
    (rationalFunctionsEquiv (X := T) (π ⁻¹ᵁ (f ⁻¹ᵁ V))).symm z ∈
        E.sections (π ⁻¹ᵁ (f ⁻¹ᵁ V)) ↔
      ∃! a : Γ(Y, V), (dominantFunctionFieldMap π).hom
        ((dominantFunctionFieldMap f).hom (Y.germToFunctionField V a)) = z := by
  haveI := dominant_preimage_nonempty f V
  haveI := dominant_preimage_nonempty π (f ⁻¹ᵁ V)
  have hiff := effective_exceptional_cartier_section_regular_descent
    hnorm hnormT π hπ E hEff hE (f ⁻¹ᵁ V) z
  have hcomm (a : Γ(Y, V)) : (dominantFunctionFieldMap f).hom (Y.germToFunctionField V a) =
      X.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom a) := by
    simpa only [Scheme.Hom.appLE_eq_app] using
      dominantFunctionFieldMap_germ f V (f ⁻¹ᵁ V) le_rfl a
  have hinj : Function.Injective (fun a : Γ(Y, V) => (dominantFunctionFieldMap π).hom
      ((dominantFunctionFieldMap f).hom (Y.germToFunctionField V a))) :=
    (dominantFunctionFieldMap π).hom.injective.comp
      ((dominantFunctionFieldMap f).hom.injective.comp (Y.germToFunctionField_injective V))
  constructor
  · intro hs
    obtain ⟨b, hb, -⟩ := hiff.mp hs
    obtain ⟨a, ha⟩ := happ V b
    have heq : (dominantFunctionFieldMap π).hom
        ((dominantFunctionFieldMap f).hom (Y.germToFunctionField V a)) = z := by
      rw [hcomm a, ha]
      exact hb
    exact ⟨a, heq, fun b hb => hinj (hb.trans heq.symm)⟩
  · rintro ⟨a, ha, -⟩
    apply hiff.mpr
    have heq : (dominantFunctionFieldMap π).hom
        (X.germToFunctionField (f ⁻¹ᵁ V) ((f.app V).hom a)) = z := by
      rw [← hcomm a]
      exact ha
    refine ⟨(f.app V).hom a, heq, fun b hb => ?_⟩
    apply X.germToFunctionField_injective (f ⁻¹ᵁ V)
    exact (dominantFunctionFieldMap π).hom.injective (hb.trans heq.symm)

end MixedFujita
