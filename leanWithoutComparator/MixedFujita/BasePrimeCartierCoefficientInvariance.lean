/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IntersectionSectionCompatibility
public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.NormalCartierLocalUnits

/-!
Equal Cartier coefficients at a normal base prime give equal pullback orders
on every actual relevant test prime. The ratio of the two local equations is
a unit in the base DVR; specialization and the actual stalk map transport that
unit upstairs. This is independent of a choice of local uniformizer.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {T Y : Scheme.{u}} [IsIntegral T] [IsIntegral Y]
  [IsLocallyNoetherian T] [IsLocallyNoetherian Y]

/-- The actual pullback coefficient above a normal base prime depends only on
the coefficient of the base Cartier divisor at that prime. -/
theorem cartierCoefficient_pullback_eq_of_base_prime_coefficient_eq
    (g : T ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
    [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (H₁ H₂ : CartierDivisor Y)
    (hH : cartierCoefficient H₁ (η : Y) = cartierCoefficient H₂ (η : Y))
    (t : CodimensionOnePoint T)
    (hη : (η : Y) ∈ closure ({g (t : T)} : Set Y)) :
    cartierCoefficient (cartierPullback g H₁) (t : T) =
      cartierCoefficient (cartierPullback g H₂) (t : T) := by
  letI := normal_codimensionOne_stalk_DVR η
  obtain ⟨f₁, hf₁⟩ := H₁.exists_isLocalEquationAt (η : Y)
  obtain ⟨f₂, hf₂⟩ := H₂.exists_isLocalEquationAt (η : Y)
  have hratio : Y.ord ((f₁ * f₂⁻¹ : Y.functionFieldˣ) : Y.functionField) (η : Y) = 0 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val,
      Scheme.ord_mul (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _)), Scheme.ord_inv,
      ← cartierCoefficient_eq_ord hf₁, ← cartierCoefficient_eq_ord hf₂, hH]
    omega
  obtain ⟨u, hu⟩ := scheme_ord_zero_exists_stalk_unit η (f₁ * f₂⁻¹) hratio
  let hs : g (t : T) ⤳ (η : Y) := specializes_iff_mem_closure.mpr hη
  let v : (Y.presheaf.stalk (g (t : T)))ˣ :=
    Units.map (Y.presheaf.stalkSpecializes hs).hom.toMonoidHom u
  have hv : algebraMap (Y.presheaf.stalk (g (t : T))) Y.functionField v =
      ((f₁ * f₂⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    have hc : Y.presheaf.stalkSpecializes hs ≫
        CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (g (t : T))) Y.functionField) =
        CommRingCat.ofHom (algebraMap (Y.presheaf.stalk (η : Y)) Y.functionField) :=
      Y.presheaf.stalkSpecializes_comp ((genericPoint_spec Y).specializes trivial) hs
    exact (ConcreteCategory.congr_hom hc (u : Y.presheaf.stalk (η : Y))).trans hu
  let w : (T.presheaf.stalk (t : T))ˣ := Units.map (g.stalkMap (t : T)).hom.toMonoidHom v
  have hw : algebraMap (T.presheaf.stalk (t : T)) T.functionField w =
      (dominantFunctionFieldMap g).hom ((f₁ * f₂⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
    change algebraMap (T.presheaf.stalk (t : T)) T.functionField
      (g.stalkMap (t : T) (v : Y.presheaf.stalk (g (t : T)))) = _
    rw [← dominantFunctionFieldMap_algebraMap, hv]
  have hz := scheme_ord_stalk_unit (t : T) w
  have hne₁ : (dominantFunctionFieldMap g).hom (f₁ : Y.functionField) ≠ 0 :=
    (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f₁).ne_zero
  have hne₂ : (dominantFunctionFieldMap g).hom (f₂ : Y.functionField) ≠ 0 :=
    (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom f₂).ne_zero
  rw [hw, Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
    Scheme.ord_mul hne₁ (inv_ne_zero hne₂),
    Scheme.ord_inv] at hz
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt g H₁ (t : T)
      (cartierLocalEquationAt_of_specializes H₁ hs f₁ hf₁)),
    cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt g H₂ (t : T)
      (cartierLocalEquationAt_of_specializes H₂ hs f₂ hf₂))]
  change T.ord ((dominantFunctionFieldMap g).hom (f₁ : Y.functionField)) (t : T) =
    T.ord ((dominantFunctionFieldMap g).hom (f₂ : Y.functionField)) (t : T)
  omega

end MixedFujita
