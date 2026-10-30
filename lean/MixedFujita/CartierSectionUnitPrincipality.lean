/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPrincipalFromSections

/-! 一つの実単元切断からCartier主因子性。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower


theorem principal_of_section_everywhere_unit
    {X : Scheme.{u}} [IsIntegral X] (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤))
    (hs : s ≠ 0)
    (hunit : ∀ (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
      IsUnit (cartierLocalCoefficient D x f hf s)) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  refine ⟨(cartierSectionUnit D s hs)⁻¹, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  refine ⟨(cartierSectionUnit D s hs)⁻¹, ?_,
    CartierDivisor.isLocalEquationAt_principalCartierDivisor x _⟩
  refine isLocalEquationAt_of_eq_unit_mul hf (hunit x f hf).unit ?_
  have hr : cartierSectionRational D s ≠ 0 := fun h => hs
    (cartierSectionRational_injective _ (h.trans (map_zero _).symm))
  rw [IsUnit.unit_spec, cartierLocalCoefficient_image, Units.val_inv_eq_inv_val,
    cartierSectionUnit_val, mul_assoc, mul_inv_cancel₀ hr, mul_one]

end MixedFujita
