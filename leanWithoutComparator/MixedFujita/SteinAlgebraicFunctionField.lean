/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalSectionsAndStein
public import MixedFujita.SteinCartierSections
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Algebraic.Basic

/-!
For a dominant Stein-type map from a normal integral scheme, every rational
function algebraic over the target function field comes from that field.
Clear denominators on one target affine open, use normality to make the
integral multiple regular on its entire preimage, and descend that regular
function. No properness or finite-type hypothesis is needed for this argument.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped nonZeroDivisors

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f]
  (happ : ∀ U : Y.Opens, Function.Surjective (f.app U).hom)
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

include happ hnorm

/-- Every rational function algebraic over the target field descends. The
denominator is cleared on a single actual affine target open. -/
theorem stein_rationalFunction_in_image_of_isAlgebraic
    (U : Y.Opens) [Nonempty U] (hU : IsAffineOpen U) (z : X.functionField)
    (hz : letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra; IsAlgebraic Y.functionField z) :
    ∃ a : Y.functionField, (dominantFunctionFieldMap f).hom a = z := by
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : Algebra Γ(Y, U) X.functionField :=
    ((dominantFunctionFieldMap f).hom.comp (Y.germToFunctionField U).hom).toAlgebra
  haveI : IsScalarTower Γ(Y, U) Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Γ(Y, U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have hpre := dominant_preimage_nonempty f U
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  haveI : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change (dominantFunctionFieldMap f).hom (Y.germToFunctionField U a) =
      X.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom a)
    simpa only [Scheme.Hom.appLE_eq_app] using
      dominantFunctionFieldMap_germ f U (f ⁻¹ᵁ U) le_rfl a
  obtain ⟨b, hb⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (M := nonZeroDivisors Γ(Y, U)) z hz.isIntegral
  haveI := normal_sections_isIntegrallyClosedIn_functionField hnorm (f ⁻¹ᵁ U)
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp
    (hb.tower_top (A := Γ(X, f ⁻¹ᵁ U)))
  obtain ⟨a, ha⟩ := happ U c
  have hnum : (dominantFunctionFieldMap f).hom (Y.germToFunctionField U a) =
      (dominantFunctionFieldMap f).hom (Y.germToFunctionField U (b : Γ(Y, U))) * z := by
    rw [dominantFunctionFieldMap_germ f U (f ⁻¹ᵁ U) le_rfl,
      Scheme.Hom.appLE_eq_app, ha]
    exact hc
  have hb0 : (b : Γ(Y, U)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.property
  have hb' : Y.germToFunctionField U (b : Γ(Y, U)) ≠ 0 := by
    simpa only [map_zero] using (Y.germToFunctionField_injective U).ne hb0
  have hden : (dominantFunctionFieldMap f).hom
      (Y.germToFunctionField U (b : Γ(Y, U))) ≠ 0 :=
    (map_ne_zero _).mpr hb'
  refine ⟨Y.germToFunctionField U a / Y.germToFunctionField U (b : Γ(Y, U)), ?_⟩
  rw [map_div₀, hnum]
  exact mul_div_cancel_left₀ z hden

/-- An algebraic Stein-type map from a normal integral source is birational.
The affine open and all descended regular functions are constructed internally. -/
theorem stein_functionFieldMap_bijective_of_isAlgebraic
    (halg : letI : Algebra Y.functionField X.functionField :=
      (dominantFunctionFieldMap f).hom.toAlgebra;
      Algebra.IsAlgebraic Y.functionField X.functionField) :
    Function.Bijective (dominantFunctionFieldMap f).hom := by
  refine ⟨(dominantFunctionFieldMap f).hom.injective, ?_⟩
  intro z
  obtain ⟨_, ⟨U, hU, rfl⟩, hgen, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  haveI : Nonempty U := ⟨⟨genericPoint Y, hgen⟩⟩
  letI : Algebra Y.functionField X.functionField :=
    (dominantFunctionFieldMap f).hom.toAlgebra
  letI : Algebra.IsAlgebraic Y.functionField X.functionField := halg
  exact stein_rationalFunction_in_image_of_isAlgebraic f happ hnorm U hU z
    (Algebra.IsAlgebraic.isAlgebraic z)

end MixedFujita
