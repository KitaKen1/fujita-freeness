/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectiveNumericallyTrivialSections
public import MixedFujita.CartierPrincipalFromSections

/-! 数値自明・生成因子の主因子性と一倍数／全整数倍の区別。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

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

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
  (hproj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
include hdim hn hproj


theorem projective_numericallyTrivial_principal_of_globallyGenerated
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (hgg : CartierIsGloballyGenerated D) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section hgg
  exact projective_numericallyTrivial_principal_of_nonzero_section hdim hn hproj D hD s hs


theorem projective_numericallyTrivial_principal_positive_multiple
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    ∃ q : ℕ, 0 < q ∧ ∃ φ : X.functionFieldˣ, q • D = principalCartierDivisor X φ := by
  obtain ⟨q, hq, hgg⟩ := hgg
  exact ⟨q, hq, projective_numericallyTrivial_principal_of_globallyGenerated hdim hn hproj
    (q • D) (cartierIsNumericallyTrivial_nsmul hD q) hgg⟩


theorem projective_numericallyTrivial_principal_of_eventually_globallyGenerated
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (hgg : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D)) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ := by
  obtain ⟨q₀, hq₀⟩ := hgg
  apply principal_of_consecutive_multiples D q₀
  · exact projective_numericallyTrivial_principal_of_globallyGenerated hdim hn hproj
      (q₀ • D) (cartierIsNumericallyTrivial_nsmul hD q₀) (hq₀ q₀ le_rfl)
  · exact projective_numericallyTrivial_principal_of_globallyGenerated hdim hn hproj
      ((q₀ + 1) • D) (cartierIsNumericallyTrivial_nsmul hD (q₀ + 1)) (hq₀ _ (by omega))

end MixedFujita
