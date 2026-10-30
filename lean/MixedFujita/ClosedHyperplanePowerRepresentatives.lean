/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierHyperplanePower
public import MixedFujita.CartierMixedIntersectionRepresentatives

/-! 閉制限した有限因子族の実Cartier代表元・射影冪と係数比較。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Closed restriction of a whole finite family supplies actual Cartier
representatives, their hyperplane powers and the exact mixed coefficient
comparison needed for dimension induction. -/
theorem closed_hyperplanePowers_exists_representatives
    (K : Type u) [Field K] {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hD : ∀ H ∈ D, CartierHasHyperplanePower K H) :
    ∃ F : List (CartierDivisor Z), F.length = D.length ∧
      (∀ J ∈ F, CartierHasHyperplanePower K J) ∧
      cartierPulledModuleMixedEulerDifference K i (CohomologyAux.unitModule Z) D 0 =
        cartierMixedEulerDifference K F 0 := by
  obtain ⟨F, hF⟩ := exists_cartier_direction_representations i D
  have hall : ∀ J ∈ F, CartierHasHyperplanePower K J := by
    induction hF with
    | nil => simp
    | @cons H J D F hHJ hDF ih =>
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · obtain ⟨a⟩ := hHJ
        exact cartierHasHyperplanePower_of_closed_representative K i H _ a (hD H (by simp))
      · exact ih (fun L hL => hD L (List.mem_cons_of_mem _ hL)) A hA
  refine ⟨F, hF.length_eq.symm, hall, ?_⟩
  exact cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K i hF 0 0
    ((Scheme.Modules.pullback i).mapIso (cartierZeroSheafIso X) ≪≫
      Scheme.Modules.pullbackObjUnitIso i ≪≫ (cartierZeroSheafIso Z).symm)

end MixedFujita
