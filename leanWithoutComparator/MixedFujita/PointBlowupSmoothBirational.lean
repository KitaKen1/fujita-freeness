/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupAdaptedCoordinates
public import MixedFujita.HironakaPrincipalizingRound
public import MixedFujita.PositiveDimensionPointedCartier
public import Hironaka.Scheme.Smooth.BlowUpSmooth

/-! Global geometric properties of the actual blow-up of a smooth closed point.
Positive dimension excludes the generic point from the centre. The existing
blow-up theorems then supply integrality, dominance, smoothness and the actual
bijection of function fields. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem pointClosureIdeal_genericPoint_notMem (hdim : 0 < topologicalKrullDim X)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    genericPoint X ∉ ((pointClosureIdeal x).support : Set X) := by
  rw [pointClosureIdeal_support_closedPoint x hx]
  exact integral_positive_dimension_genericPoint_ne_closedPoint hdim x hx

theorem pointBlowup_isIntegral [IsLocallyNoetherian X]
    (hdim : 0 < topologicalKrullDim X) (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIntegral (pointClosureIdeal x).blowUp :=
  blowUp_isIntegral_of_genericPoint_notMem_support _ (pointClosureIdeal_genericPoint_notMem hdim x hx)

theorem pointBlowup_isDominant (hdim : 0 < topologicalKrullDim X)
    (x : X) (hx : IsClosed ({x} : Set X)) : IsDominant (pointClosureIdeal x).blowUpπ :=
  blowUp_isDominant_of_genericPoint_notMem_support _ (pointClosureIdeal_genericPoint_notMem hdim x hx)

theorem pointBlowup_functionField_bijective
    (hdim : 0 < topologicalKrullDim X) (x : X) (hx : IsClosed ({x} : Set X))
    [IsIntegral (pointClosureIdeal x).blowUp] [IsDominant (pointClosureIdeal x).blowUpπ] :
    Function.Bijective (dominantFunctionFieldMap (pointClosureIdeal x).blowUpπ).hom := by
  apply dominantFunctionFieldMap_bijective_of_isIso_stalkMap
  apply blowUp_isIso_stalkMap_of_notMem_support
  rw [dominant_map_genericPoint]
  exact pointClosureIdeal_genericPoint_notMem hdim x hx

variable {K : Type u} [Field K] [IsAlgClosed K] [X.Over (Spec (.of K))]
  [Smooth (X ↘ Spec (.of K))] {n : ℕ}

theorem smooth_closedPoint_pointBlowup_smoothOfRelativeDimension
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X)) :
    SmoothOfRelativeDimension n ((pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))) := by
  have := geometricSmoothScheme_relativeDimension (K := K) n hn
  have := pointClosure_closedPoint_smoothOfRelativeDimension_zero (K := K) x hx
  have : SmoothOfRelativeDimension (n - n) (pointClosureι x ≫ (X ↘ Spec (.of K))) := by simpa
  exact smoothOfRelativeDimension_blowUpπ_comp (X ↘ Spec (.of K)) n n (pointClosureIdeal x) le_rfl

end MixedFujita
