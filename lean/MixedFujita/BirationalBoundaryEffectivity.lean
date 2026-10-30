/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalBirationalOrders
public import MixedFujita.NormalBirationalPrimeLifts

/-!
At an actual codimension-one stalk isomorphism, the order of the pulled rational
top form agrees with the order downstairs. The Jacobian contributes zero.
Proper birational lifts of normal target primes therefore descend effectiveness
of the crepant boundary, without assuming either scheme is globally smooth.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y] [IsLocallyNoetherian X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
  (hf : Function.Bijective (dominantFunctionFieldAlgHom (K := K) f))

/-- A rational top form has the same prime order at an actual birational stalk
isomorphism, using only charts at the two points. -/
theorem crepantPullbackFormUnit_order_of_stalkMap_bijective
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (cX : EtaleChart K X n)
    (x : CodimensionOnePoint X) (hy : Order.coheight (f (x : X)) = 1)
    [IsDiscreteValuationRing (Y.presheaf.stalk (f (x : X)))]
    [IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (hb : Function.Bijective (f.stalkMap (x : X)))
    (c : EtaleChart K Y n) (hc : f (x : X) ∈ c.U)
    (c' : EtaleChart K X n) (hc' : (x : X) ∈ c'.U) :
    X.ord ((crepantPullbackFormUnit f hf cY fY cX *
      etaleChartCanonicalEquation cX c' : X.functionFieldˣ) : X.functionField) (x : X) =
    Y.ord ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) :
      Y.functionField) (f (x : X)) := by
  have hJ : (dominantFunctionFieldMap f).hom
      (etaleChartCanonicalEquation cY c : Y.functionField) *
      chartRelativeJacobianDet f c c' = chartRelativeJacobianDet f cY cX *
      (etaleChartCanonicalEquation cX c' : X.functionField) :=
    chartRelativeJacobianDet_change f cY c cX c'
  have hval : ((crepantPullbackFormUnit f hf cY fY cX *
      etaleChartCanonicalEquation cX c' : X.functionFieldˣ) : X.functionField) =
      (dominantFunctionFieldMap f).hom
        ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField) *
      chartRelativeJacobianDet f c c' := by
    simp only [crepantPullbackFormUnit, Units.val_mul, Units.coe_map,
      IsUnit.unit_spec, map_mul]
    linear_combination (-((dominantFunctionFieldMap f).hom (fY : Y.functionField))) * hJ
  have hφ : (dominantFunctionFieldMap f).hom
      ((fY * etaleChartCanonicalEquation cY c : Y.functionFieldˣ) : Y.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  rw [hval, X.ord_mul hφ
    (isUnit_chartRelativeJacobianDet_of_bijective f hf c c').ne_zero,
    scheme_ord_pullback_of_stalkMap_bijective f x hy hb,
    chartRelativeJacobianDet_ord_zero_of_stalkMap_bijective f x hb c hc c' hc', add_zero]

/-- An effective crepant boundary upstairs is effective downstairs on normal
schemes. Actual prime lifts and their stalk isomorphisms are supplied internally. -/
theorem logPairBoundaryEffective_of_crepant_pullback [IsProper f]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcovX : CodimOneChartCovered n K X)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor Y) (cX : EtaleChart K X n)
    (heff : LogPairBoundaryEffective cX (crepantPullbackFormUnit f hf cY fY cX) d
      (cartierPullback f D)) : LogPairBoundaryEffective cY fY d D := by
  intro c y hy hcoh
  obtain ⟨x, hxy, hb⟩ :=
    proper_birational_exists_normal_prime_lift hnormY f hf ⟨y, hcoh⟩
  have hfx : Order.coheight (f (x : X)) = 1 := by simpa only [hxy] using hcoh
  letI := hnormY (f (x : X))
  letI := hnormX (x : X)
  letI := normal_codimensionOne_stalk_DVR (⟨f (x : X), hfx⟩ : CodimensionOnePoint Y)
  letI := normal_codimensionOne_stalk_DVR x
  obtain ⟨c', hc'⟩ := hcovX (x : X) x.property
  have h := heff c' (x : X) hc' x.property
  have hc : f (x : X) ∈ c.U := by simpa only [hxy] using hy
  rw [crepantPullbackFormUnit_order_of_stalkMap_bijective f hf cY fY cX x hfx hb c hc c' hc',
    cartierCoefficient_pullback_of_stalkMap_bijective f x hfx hb D] at h
  simpa only [hxy] using h

end MixedFujita
