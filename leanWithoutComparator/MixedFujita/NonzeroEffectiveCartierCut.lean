/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutDimension
public import MixedFujita.NormalCartierCoefficientExt

/-! 正常源の非零有効Cartier因子から非空切断を内部構成。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- On a normal source a NONZERO effective Cartier divisor has a
nonempty ACTUAL Cartier cut; emptiness is not a hidden premise. -/
theorem normal_nonzero_effectiveCartierCut_nonempty
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (G : CartierDivisor X) (hG : G.IsEffective) (hne : G ≠ 0) :
    Nonempty (effectiveCartierIdealSheaf G hG).subscheme := by
  by_contra hempty
  let : IsEmpty (effectiveCartierIdealSheaf G hG).subscheme := not_nonempty_iff.mp hempty
  have hsupp : ((effectiveCartierIdealSheaf G hG).support : Set X) = ∅ := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.range_eq_empty_iff.mpr inferInstance
  apply hne
  apply cartierDivisor_eq_of_forall_coefficient_eq hnorm G 0
  intro z
  have hz : (z : X) ∉ (effectiveCartierIdealSheaf G hG).support := by
    change (z : X) ∉ ((effectiveCartierIdealSheaf G hG).support : Set X)
    rw [hsupp]
    simp
  rw [cartierCoefficient_eq_zero_of_notMem_support_effectiveCartierIdealSheaf G hG (z : X) hz]
  exact (cartierCoefficient_zero (z : X)).symm

end MixedFujita
