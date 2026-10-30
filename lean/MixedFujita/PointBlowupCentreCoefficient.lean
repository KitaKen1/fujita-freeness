/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCComponentCartier
public import MixedFujita.DVRVanishingOrder
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import MixedFujita.SuppliedEtaleCartierBlowup
public import MixedFujita.EtaleDVRCoordinateOrder
public import MixedFujita.ExceptionalCentreClassification

/-! Recover the coefficient of an effective Cartier divisor from a generator
of its actual stalk ideal. On a model mapping to the blow-up of a smooth
closed point, a bijective stalk map at the retained prime transports an
etale exceptional coordinate to a DVR uniformizer. Thus the divisor of
the pulled point-centre ideal has coefficient one there. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- A regular stalk-ideal generator determines the effective coefficient. -/
theorem effectiveCartier_coefficient_of_stalkIdeal_span
    (D : CartierDivisor X) (hD : D.IsEffective) (t : CodimensionOnePoint X)
    [IsDiscreteValuationRing (X.presheaf.stalk (t : X))]
    (u : X.presheaf.stalk (t : X)) (hu : u ≠ 0)
    (hI : (effectiveCartierIdealSheaf D hD).stalkIdeal (t : X) = Ideal.span {u})
    (m : ℕ) (hm : localAdicOrder (X.presheaf.stalk (t : X)) u = (m : ℕ∞)) :
    cartierCoefficient D (t : X) = (m : ℤ) := by
  obtain ⟨U, htU, hne, a, ha, hEq⟩ := exists_affineOpen_regularEquation_of_isEffective D hD (t : X)
  let v := X.presheaf.germ U.1 (t : X) htU a
  have hspan : Ideal.span {v} = Ideal.span {u} := by
    have h := (effectiveCartierIdealSheaf D hD).stalkIdeal_eq_map_germ U htU
    rw [effectiveCartierIdealSheaf_ideal_eq_span D hD U a ha hEq,
      Ideal.map_span, Set.image_singleton] at h
    exact h.symm.trans hI
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hv : v ≠ 0 := by
    intro hv0
    apply hu
    rw [← hw, hv0, zero_mul]
  have horder : localAdicOrder (X.presheaf.stalk (t : X)) v = (m : ℕ∞) := by
    rw [← hw, dvr_localAdicOrder_eq_addVal, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr w.isUnit, add_zero] at hm
    rwa [dvr_localAdicOrder_eq_addVal]
  rw [cartierCoefficient_eq_ord
    (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEq htU), regularEquationRationalUnit_val,
    ← X.algebraMap_germ_eq_germToFunctionField htU]
  exact scheme_ord_regular_eq_localAdicOrder_nat t v hv m horder


variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseOpenAlgebra

set_option maxHeartbeats 1400000 in
/-- The actual pulled point-centre divisor has multiplicity one at a prime
where the lift to the point blow-up induces a stalk isomorphism. -/
theorem pointBlowup_centre_divisor_coefficient_one_at_stalk_iso
    (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X))
    (ρ : T ⟶ X) [ρ.IsOver (Spec (.of K))]
    (g : T ⟶ (pointClosureIdeal x).blowUp) (hg : g ≫ (pointClosureIdeal x).blowUpπ = ρ)
    (t : CodimensionOnePoint T) (ht : ρ (t : T) = x)
    (hgiso : Function.Bijective (g.stalkMap (t : T)))
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = (pointClosureIdeal x).comap ρ) :
    cartierCoefficient E (t : T) = 1 := by
  classical
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (T ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) t
  let I := pointClosureIdeal x
  let π := I.blowUpπ
  let : I.blowUp.Over (Spec (.of K)) := ⟨π ≫ (X ↘ Spec (.of K))⟩
  have : π.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : g.IsOver (Spec (.of K)) := ⟨by
    change g ≫ (π ≫ (X ↘ Spec (.of K))) = T ↘ Spec (.of K)
    rw [← Category.assoc, hg]
    exact HomIsOver.comp_over (f := ρ) (S := Spec (.of K))⟩
  obtain ⟨completion, -⟩ := geometricSmoothScheme_closedPoint_exists_stalkCoordinates (K := K) n hn x hx
  obtain ⟨c, hxc, hall⟩ := smoothCartier_suppliedCompletion_pointBlowup_etale hn x hx completion
  have hq : π (g (t : T)) = x := by
    change (g ≫ π) (t : T) = x
    rw [hg]
    exact ht
  obtain ⟨k, τ, hτ, hI, -, -, -⟩ := hall (g (t : T)) hq
  let β := schemeStalkMapAlgHom (K := K) g (t : T)
  have hβ : Function.Bijective β := hgiso
  have hβet : β.toRingHom.FormallyEtale :=
    ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective hβ)
  let z := β.comp τ
  have hz : z.toRingHom.FormallyEtale := formallyEtale_comp β hβet τ hτ
  have hIT : (effectiveCartierIdealSheaf E hE).stalkIdeal (t : T) = Ideal.span {z (MvPolynomial.X k)} := by
    rw [hEI, ← hg, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.stalkIdeal_comap, hI, Ideal.map_span, Set.image_singleton]
    rfl
  have hEsupport : (t : T) ∈ (effectiveCartierIdealSheaf E hE).support := by
    rw [hEI, Scheme.IdealSheafData.support_comap]
    change ρ (t : T) ∈ (pointClosureIdeal x).support
    rw [ht]
    change x ∈ ((pointClosureIdeal x).support : Set X)
    rw [pointClosureIdeal_support_closedPoint x hx]
    rfl
  have hnon : ¬ IsUnit (z (MvPolynomial.X k)) :=
    (IsLocalRing.mem_maximalIdeal _).mp
      (((effectiveCartierIdealSheaf E hE).mem_support_iff_stalkIdeal_le_maximalIdeal
        (t : T)).mp hEsupport (by rw [hIT]; exact Ideal.subset_span rfl))
  have hne : z (MvPolynomial.X k) ≠ 0 := (etaleDVR_coordinate_irreducible z hz k hnon).ne_zero
  simpa only [Nat.cast_one] using effectiveCartier_coefficient_of_stalkIdeal_span E hE t _ hne hIT 1
    (etaleDVR_coordinate_localAdicOrder z hz k hnon)

end MixedFujita
