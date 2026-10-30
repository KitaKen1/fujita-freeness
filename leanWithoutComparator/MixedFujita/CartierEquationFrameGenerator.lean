/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModulePullbackFrameGenerators

/-!
The frame generator of O(-D) for a regular equation a of an effective
Cartier divisor maps to the actual regular section a under O(-D) -> O.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem cartierNegative_regularEquation_restrict (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (ha : a ≠ 0)
    (hD : rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U a ha)) =
      D |_ U) :
    rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U a ha)⁻¹) =
      (-D) |_ U := by
  change rationalUnitClass X U (-(Additive.ofMul (regularEquationRationalUnit X U a ha))) =
    (cartierDivisorSheaf X).1.map (homOfLE le_top).op (-D)
  rw [map_neg, map_neg]
  exact congrArg Neg.neg hD

noncomputable def negativeCartierRegularEquationFrame (D : CartierDivisor X)
    (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (ha : a ≠ 0)
    (hD : rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U a ha)) =
      D |_ U) : (-D).sheaf.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf :=
  cartierOpenRestrictFrameIso (-D) U (regularEquationRationalUnit X U a ha)⁻¹
    (cartierNegative_regularEquation_restrict D U a ha hD)

theorem negativeCartierRegularEquationFrameGenerator_image (D : CartierDivisor X)
    (hE : D.IsEffective) (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (ha : a ≠ 0)
    (hD : rationalUnitClass X U (Additive.ofMul (regularEquationRationalUnit X U a ha)) =
      D |_ U) :
    Scheme.Modules.Hom.app (negativeCartierToUnit X D hE) U
      (moduleOpenFrameGenerator (-D).sheaf U (negativeCartierRegularEquationFrame D U a ha hD)) =
        a := by
  let t := moduleOpenFrameGenerator (-D).sheaf U (negativeCartierRegularEquationFrame D U a ha hD)
  have ht := moduleOpenFrameGenerator_coefficient (-D).sheaf U
    (negativeCartierRegularEquationFrame D U a ha hD)
  rw [show moduleRestrictFrameOverIso (-D).sheaf U
      (negativeCartierRegularEquationFrame D U a ha hD) =
    cartierOpenFrameIso (-D) U (regularEquationRationalUnit X U a ha)⁻¹
      (cartierNegative_regularEquation_restrict D U a ha hD) from
        moduleRestrictFrameOverIso_roundTrip _ _ _] at ht
  have hc := cartierOpenCoefficient_image (-D) U
    (regularEquationRationalUnit X U a ha)⁻¹
    (cartierNegative_regularEquation_restrict D U a ha hD) U le_rfl t
  change X.germToFunctionField U
      (moduleOverFrameCoefficient (-D).sheaf U
        (cartierOpenFrameIso (-D) U (regularEquationRationalUnit X U a ha)⁻¹
          (cartierNegative_regularEquation_restrict D U a ha hD)) U le_rfl t) = _ at hc
  rw [ht, map_one] at hc
  apply X.germToFunctionField_injective U
  rw [← rationalFunctionsEquiv_toRationalFunctions_app,
    negativeCartierToUnit_app, toRationalFunctions_negativeCartierRegularSection]
  have hm := congrArg (fun b : X.functionField =>
    (regularEquationRationalUnit X U a ha : X.functionField) * b) hc
  rw [mul_one, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at hm
  simpa only [regularEquationRationalUnit_val] using hm.symm

end MixedFujita
