/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineCartierNumericalTriviality
public import MixedFujita.KltPairs

/-! Over an affine base, the relative and ordinary canonical adjoint nef
conditions agree. The exact equality retains both the base canonical pullback
and the Jacobian principal divisor before their numerical contributions vanish.
No properness over the field or vanishing theorem is assumed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsAffine X]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (cX : EtaleChart K X n) (cT : EtaleChart K T n)

omit [IsAffine X] in
/-- Exact Cartier adjoint identity, including the reference-chart Jacobian. -/
theorem affine_relative_adjoint_eq_ordinary
    (Q F : CartierDivisor T) (d : ℕ) :
    d • (Q - birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover) - F =
      (d • (Q - smoothCanonicalDivisor cT) - F +
        cartierPullback ρ (d • smoothCanonicalDivisor cX)) +
      principalCartierDivisor T
        (((isUnit_chartRelativeJacobianDet_of_bijective ρ hρ cX cT).unit ^ d)⁻¹) := by
  rw [principalCartierDivisor_inv, principalCartierDivisor_power, cartierPullback_nsmul]
  unfold birationalRelativeCanonicalDivisor relativeCanonicalDivisor smoothCanonicalDivisor
  module

/-- All base canonical and Jacobian corrections have zero curve degree. -/
theorem affine_relative_adjoint_nef_iff_ordinary
    (Q F : CartierDivisor T) (d : ℕ) :
    CartierIsNef K
      (d • (Q - birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover) - F) ↔
      CartierIsNef K (d • (Q - smoothCanonicalDivisor cT) - F) := by
  rw [affine_relative_adjoint_eq_ordinary ρ hρ cX cT,
    cartierIsNef_add_principal_iff, cartierIsNef_add_affine_pullback_iff]

/-- The negative relative adjoint in the original connectedness input has
exactly the same nef condition as the ordinary negative adjoint. -/
theorem affine_negative_relative_adjoint_nef_iff_ordinary
    (B : CartierDivisor T) (d : ℕ) :
    CartierIsNef K
      (-(d • birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover + B)) ↔
      CartierIsNef K (-(d • smoothCanonicalDivisor cT + B)) := by
  simpa only [zero_sub, smul_neg, sub_eq_add_neg, neg_add_rev, add_comm, add_zero, zero_add] using
    affine_relative_adjoint_nef_iff_ordinary ρ hρ cX cT 0 B d

/-- The exact canonical correction preserves actual global generation as well. -/
theorem affine_relative_adjoint_globallyGenerated_iff_ordinary
    (Q F : CartierDivisor T) (d : ℕ) :
    CartierIsGloballyGenerated
      (d • (Q - birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover) - F) ↔
      CartierIsGloballyGenerated (d • (Q - smoothCanonicalDivisor cT) - F) := by
  rw [affine_relative_adjoint_eq_ordinary ρ hρ cX cT,
    cartierIsGloballyGenerated_principal_shift_iff,
    cartierIsGloballyGenerated_add_affine_pullback_iff]

end MixedFujita
