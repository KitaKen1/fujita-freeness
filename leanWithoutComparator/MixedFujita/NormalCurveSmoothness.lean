/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NormalCodimensionOneCharts
public import Hironaka.Resolution.Algebraic.Hir64.SingleCenterTools
public import TauCeti.Topology.KrullDimension

/-! 完全体上の正規整曲線の実smooth性。 See reports/check-214-curve-f1-f2-integration.json for the verified scope. -/

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


theorem normalCurve_smooth
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (hX : topologicalKrullDim X = 1)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    Smooth (X ↘ Spec (CommRingCat.of K)) := by
  apply (Scheme.smooth_iff_isRegular _).mpr
  constructor
  intro x
  have hdim : coheight x ≤ 1 := by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hX.le
  by_cases hx0 : coheight x = 0
  · have hmax := Order.coheight_eq_zero.mp hx0
    have hgen : x ≤ genericPoint X := Scheme.le_iff_specializes.mpr
      ((genericPoint_spec X).specializes (Set.mem_univ x))
    have heq : x = genericPoint X :=
      ((Scheme.le_iff_specializes.mp (hmax hgen)).antisymm
        (Scheme.le_iff_specializes.mp hgen)).eq
    subst x
    exact Hironaka.Resolution.isRegularAt_genericPoint_of_isIntegral
  · have hx1 : coheight x = 1 := le_antisymm hdim (Order.one_le_iff_ne_zero.mpr hx0)
    let := hnorm x
    exact normal_codimensionOne_stalk_regular ⟨x, hx1⟩

end MixedFujita
