/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveFiniteAffineNeighborhood
public import MixedFujita.FiniteComplementCurveCohomology

/-!
An actual closed immersion into polynomial projective space over an infinite
field supplies the common affine neighborhoods. For a proper integral curve,
this constructs a two-affine cover and derives high cohomology vanishing.
For a proper smooth integral curve, every invertible sheaf has finite
cohomology in all degrees. No affine-neighborhood, cover or cohomology
assumption is needed. Existence of a projective embedding is not proved here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u

theorem polynomialProjective_closedImmersion_isProper_over_field
    {K : Type u} [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] {m : ℕ}
    (e : Y ⟶ polynomialProjectiveScheme m K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase m K = Y ↘ Spec (CommRingCat.of K)) :
    IsProper (Y ↘ Spec (CommRingCat.of K)) := by
  let := polynomialProjectiveToBase_isProper m K
  rw [← he]
  infer_instance

variable {K : Type u} [Field K] [Infinite K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
  {m : ℕ} (e : Y ⟶ polynomialProjectiveScheme m K) [IsClosedImmersion e]

include e

theorem properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover
    (hY : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ :=
  properIntegralCurve_exists_twoAffine_cover_of_finiteClosedAffineNeighborhoods (K := K)
    hY (fun Z hZ _ ↦ polynomialProjective_affineHom_finiteSubset_affine_neighborhood e Z hZ)

theorem properProjectivelyEmbeddedIntegralCurve_cohomology_vanish
    (hY : topologicalKrullDim Y ≤ 1) (M : Y.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Scheme.Modules.Cohomology M q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover e hY
  exact properTwoAffine_cohomology_vanish (K := K) M hU hV hUV q hq

theorem properProjectivelyEmbeddedIntegralCurve_eulerCharBelow_eq_two
    (hY : topologicalKrullDim Y ≤ 1) (M : Y.Modules) [M.IsQuasicoherent]
    (n : ℕ) (hn : 2 ≤ n) :
    Scheme.Modules.eulerCharBelow K Y M n = Scheme.Modules.eulerCharBelow K Y M 2 := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover e hY
  exact properTwoAffine_eulerCharBelow_eq_two M hU hV hUV n hn

theorem properSmoothProjectivelyEmbeddedCurve_finiteDimensional_invertible_cohomology
    [Smooth (Y ↘ Spec (CommRingCat.of K))] (hY : topologicalKrullDim Y = 1)
    (M : Y.Modules) [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y M] (q : ℕ) :
    FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover e hY.le
  exact properSmoothTwoAffineCurve_finiteDimensional_invertible_cohomology hY M hU hV hUV q

variable {X : Scheme.{u}} [IsIntegral X]

theorem properSmoothProjectivelyEmbeddedCurve_finiteDimensional_cartierPullback_cohomology
    [Smooth (Y ↘ Spec (CommRingCat.of K))] (hY : topologicalKrullDim Y = 1)
    (D : CartierDivisor X) (φ : Y ⟶ X) (q : ℕ) : FiniteDimensional K
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback φ).obj D.sheaf) q) := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover e hY.le
  exact properSmoothTwoAffineCurve_finiteDimensional_cartierPullback_cohomology
    hY D φ hU hV hUV q

theorem cartierCurvePullbackDegree_eq_eulerDifference_of_projectiveEmbedding
    (hY : topologicalKrullDim Y ≤ 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (n : ℕ) (hn : 2 ≤ n) :
    cartierCurvePullbackDegree (K := K) D φ =
      Scheme.Modules.eulerCharBelow K Y ((Scheme.Modules.pullback φ).obj D.sheaf) n -
        Scheme.Modules.eulerCharBelow K Y (SheafOfModules.unit Y.ringCatSheaf) n := by
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    properProjectivelyEmbeddedIntegralCurve_exists_twoAffine_cover e hY
  exact cartierCurvePullbackDegree_eq_eulerDifference_of_twoAffine D φ hU hV hUV n hn

end MixedFujita
