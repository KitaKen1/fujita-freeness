/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.ProperClosedImmersionDimension

/-! 実有効Cartier切断の一般点回避と普通のKrull次元降下。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The actual effective Cartier subscheme misses the generic point, so its
closed immersion is a proper subset, even when the cut is nonreduced. -/
theorem effectiveCartierCut_range_ne_univ
    {X : Scheme.{u}} [IsIntegral X] (H : CartierDivisor X) (hH : H.IsEffective) :
    Set.range (effectiveCartierIdealSheaf H hH).subschemeι ≠ Set.univ := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  intro h
  apply genericPoint_notMem_support_effectiveCartierIdealSheaf H hH
  change genericPoint X ∈ ((effectiveCartierIdealSheaf H hH).support : Set X)
  rw [h]
  trivial


/-- The actual effective Cartier cut lowers ordinary dimension. No
integrality or reducedness assumption on the cut is introduced. -/
theorem effectiveCartierCut_topologicalKrullDim_le
    {X : Scheme.{u}} [IsIntegral X] (H : CartierDivisor X) (hH : H.IsEffective)
    (n : ℕ) (hdim : topologicalKrullDim X ≤ (n + 1 : ℕ)) :
    topologicalKrullDim (effectiveCartierIdealSheaf H hH).subscheme ≤ n :=
  properClosedImmersion_topologicalKrullDim_le_predecessor
    (effectiveCartierIdealSheaf H hH).subschemeι
    (effectiveCartierCut_range_ne_univ H hH) n hdim

end MixedFujita
