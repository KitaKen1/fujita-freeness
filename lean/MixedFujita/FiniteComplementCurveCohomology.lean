/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IntegralCurveFiniteComplement
public import MixedFujita.ProperTwoAffineCurveCohomology

/-!
The finite complement construction supplies a two-affine cover once finite
closed subsets have common affine neighborhoods. Properness supplies the
Noetherian scheme structure. No cover or cohomology input is assumed below;
the common affine neighborhood theorem is still an explicit geometric input.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]

include K in
theorem properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods
    (hY : topologicalKrullDim Y ≤ 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  exact integralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods hY hAF

include K in
theorem properIntegralCurve_cohomology_vanish_of_finiteClosedAffineNeighborhoods
    (hY : topologicalKrullDim Y ≤ 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V)
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology M q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K) hY hAF
  exact properTwoAffine_cohomology_vanish (K := K) M hU hV hUV q hq

theorem properIntegralCurve_eulerCharBelow_eq_two_of_finiteClosedAffineNeighborhoods
    (hY : topologicalKrullDim Y ≤ 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V)
    (M : Y.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Scheme.Modules.eulerCharBelow K Y M n = Scheme.Modules.eulerCharBelow K Y M 2 := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K) hY hAF
  exact properTwoAffine_eulerCharBelow_eq_two M hU hV hUV n hn

theorem properSmoothCurve_finiteDimensional_invertible_cohomology_of_finiteClosedAffineNeighborhoods
    [Smooth (Y ↘ Spec (CommRingCat.of K))] (hY : topologicalKrullDim Y = 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V)
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M] (q : ℕ) :
    FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K) hY.le hAF
  exact properSmoothTwoAffineCurve_finiteDimensional_invertible_cohomology hY M hU hV hUV q

variable {X : Scheme.{u}} [IsIntegral X]

theorem properSmoothCurve_finiteDimensional_cartierPullback_cohomology_of_finiteClosedAffineNeighborhoods
    [Smooth (Y ↘ Spec (CommRingCat.of K))] (hY : topologicalKrullDim Y = 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V)
    (D : CartierDivisor X) (φ : Y ⟶ X) (q : ℕ) : FiniteDimensional K
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K) hY.le hAF
  exact properSmoothTwoAffineCurve_finiteDimensional_cartierPullback_cohomology
    hY D φ hU hV hUV q

theorem cartierCurvePullbackDegree_eq_eulerDifference_of_finiteClosedAffineNeighborhoods
    (hY : topologicalKrullDim Y ≤ 1)
    (hAF : ∀ Z : Set Y, Z.Finite → IsClosed Z →
      ∃ V : Y.Opens, IsAffineOpen V ∧ Z ⊆ V)
    (D : CartierDivisor X) (φ : Y ⟶ X) (n : ℕ) (hn : 2 ≤ n) :
    cartierCurvePullbackDegree (K := K) D φ =
      Scheme.Modules.eulerCharBelow K Y ((Scheme.Modules.pullback φ).obj D.sheaf) n -
        Scheme.Modules.eulerCharBelow K Y (SheafOfModules.unit Y.ringCatSheaf) n := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K) hY hAF
  exact cartierCurvePullbackDegree_eq_eulerDifference_of_twoAffine D φ hU hV hUV n hn

end MixedFujita
