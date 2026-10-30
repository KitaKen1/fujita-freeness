/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalTriviality
public import MixedFujita.CartierNefPullback

/-! 非零切断のある数値自明因子の実支配引き戻し。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

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


theorem cartierIsNumericallyTrivial_pullback_of_nonzero_section
    {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    CartierIsNumericallyTrivial K (cartierPullback ρ D) := by
  intro C _ _ _ _ hC ψ hψ
  rw [cartierCurvePullbackDegree_cartierPullback (K := K) hC ρ ψ D s hs]
  apply hD C hC (ψ ≫ ρ)
  rw [Category.assoc, HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K)), hψ]

end MixedFujita
