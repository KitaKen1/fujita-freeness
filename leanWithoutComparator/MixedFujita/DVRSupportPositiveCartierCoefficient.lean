/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.NormalCartierLocalUnits
public import MixedFujita.EffectiveCartierCoefficientSupport

/-! 実DVR素点の有効Cartier台から実係数の正値性。 See reports/check-268-internal-lc-center-isolation.json for the verified scope. ACTUAL minimal-lc-center isolation now internally constructs the original center ideal finite system, SAME-original-family principalization/residual Bertini, source perturbation, shared SNC model, old-critical positivity and placement. A contained lc center obstructs every positive perturbation, forcing a positive old-critical coefficient on ANY joint model by finite-LC-threshold contradiction. Arbitrary anchor denominators are normalized retaining actual centers. Original positive-numerical klt BPF assumptions construct an isolated restricted-numerical-zero center; EXPLICIT usual H1 KV gives exact-center original mL lifting. Zero-dimensional minimal centers yield original nonvanishing under usual KV. Positive-dimensional numerical-zero-center nonvanishing, general KV, the original nu=0 branch, unconditional BPF and full F1/F2 remain unproved. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory Filter
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable


/-- At an ACTUAL DVR prime, membership in the support of an effective Cartier
ideal forces a STRICTLY POSITIVE actual prime coefficient. Zero order would
make its actual regular equation a stalk unit. -/
theorem effective_cartier_coefficient_pos_of_mem_support_at_dvr
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (D : CartierDivisor X) (hD : D.IsEffective) (x : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hx : (x : X) ∈ (effectiveCartierIdealSheaf D hD).support) :
    0 < cartierCoefficient D (x : X) := by
  have hnonneg := cartierCoefficient_nonneg_of_isEffective D hD (x : X)
  by_contra hn
  have hzero : cartierCoefficient D (x : X) = 0 := by omega
  obtain ⟨U, hxU, hne, a, ha, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective D hD (x : X)
  let := hne
  let f := regularEquationRationalUnit X U.1 a ha
  have hloc : D.IsLocalEquationAt (x : X) f := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq hxU
  have hord : X.ord (f : X.functionField) (x : X) = 0 := by
    rw [← cartierCoefficient_eq_ord hloc]
    exact hzero
  obtain ⟨u, hu⟩ := scheme_ord_zero_exists_stalk_unit x f hord
  have hgerm : X.presheaf.germ U.1 (x : X) hxU a = (u : X.presheaf.stalk (x : X)) := by
    apply IsFractionRing.injective (X.presheaf.stalk (x : X)) X.functionField
    rw [X.algebraMap_germ_eq_germToFunctionField hxU, hu]
    rfl
  have hbasic : (x : X) ∈ X.basicOpen a :=
    (X.mem_basicOpen a (x : X) hxU).mpr (hgerm.symm ▸ u.isUnit)
  rw [(effectiveCartierIdealSheaf D hD).mem_support_iff_of_mem (U := U) hxU,
    effectiveCartierIdealSheaf_ideal_eq_span D hD U a ha hEq, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton] at hx
  exact hx hbasic

end MixedFujita
