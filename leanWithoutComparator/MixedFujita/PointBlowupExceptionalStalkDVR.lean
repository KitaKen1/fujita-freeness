/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupExceptionalDVR
public import MixedFujita.PointBlowupChartStalk
public import MixedFujita.LocalAdicRestriction
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Chart

/-! The constructed exceptional prime gives an actual point of the original
scheme's blow-up. Its actual stalk is isomorphic to the constructed DVR,
compatibly with every element of the actual chart ring. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem affineBlowupChartToStalk_exists_ringEquiv {R : Type u} [CommRing R]
    (I : Ideal R) (a : I) (p : Spec (.of (affineBlowUpAlgebra I a))) :
    ∃ e : (affineBlowUp I).presheaf.stalk (affineBlowUp.chart I a p) ≃+*
        Localization.AtPrime p.asIdeal,
      ∀ c, e (affineBlowupChartToStalk I a p c) = algebraMap _ _ c := by
  obtain ⟨e, he⟩ := exists_ringEquiv_stalk_chart I a p
  refine ⟨e, fun c => ?_⟩
  apply e.symm.injective
  rw [RingEquiv.symm_apply_apply]
  apply (ConcreteCategory.bijective_of_isIso ((affineBlowUp.chart I a).stalkMap p)).1
  rw [he]
  change (asIso ((affineBlowUp.chart I a).stalkMap p)).hom
    ((asIso ((affineBlowUp.chart I a).stalkMap p)).inv (specGerm p c)) = specGerm p c
  exact Iso.inv_hom_id_apply _ _

theorem localPointBlowup_exceptionalPrime_over {K R : Type u} [Field K] [CommRing R]
    [Algebra K R] [IsLocalRing R] {n : ℕ}
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (k : Fin n) :
    let a : IsLocalRing.maximalIdeal R := ⟨ψ (MvPolynomial.X k),
      localTaylorCoordinate_mem_maximalIdeal ψ T hX hord k⟩
    let p := localPointBlowupExceptionalPrime ψ T hX hord hmax k
    affineBlowUp.π (IsLocalRing.maximalIdeal R)
      (affineBlowUp.chart (IsLocalRing.maximalIdeal R) a p) = IsLocalRing.closedPoint R := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let a : IsLocalRing.maximalIdeal R := ⟨ψ (MvPolynomial.X k), hψ k⟩
  let p := localPointBlowupExceptionalPrime ψ T hX hord hmax k
  let β := algebraMap R (affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) a)
  change (affineBlowUp.chart (IsLocalRing.maximalIdeal R) a ≫ affineBlowUp.π _) p = _
  rw [affineBlowUp.chart_π]
  apply PrimeSpectrum.ext
  change p.asIdeal.comap β = IsLocalRing.maximalIdeal R
  symm
  apply (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
  · exact (inferInstance : (p.asIdeal.comap β).IsPrime).ne_top
  · rw [← Ideal.map_le_iff_le_comap, localPointBlowupPolynomialMap_exceptionalIdeal _ ψ hψ k]
    exact le_rfl

variable {X : Scheme.{u}}

set_option maxHeartbeats 500000 in
theorem pointBlowupChartToStalk_exists_ringEquiv (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a))) :
    ∃ e : (pointClosureIdeal x).blowUp.presheaf.stalk
        (pointBlowupLocalMap x (affineBlowUp.chart _ a p)) ≃+* Localization.AtPrime p.asIdeal,
      ∀ c, e (pointBlowupChartToStalk x a p c) = algebraMap _ _ c := by
  obtain ⟨e, he⟩ := affineBlowupChartToStalk_exists_ringEquiv _ a p
  let e₀ := (pointBlowupLocalStalkIso x (affineBlowUp.chart _ a p)).commRingCatIsoToRingEquiv
  refine ⟨e₀.trans e, fun c => ?_⟩
  change e (e₀ (e₀.symm (affineBlowupChartToStalk _ a p c))) = _
  rw [RingEquiv.apply_symm_apply]
  exact he c


set_option maxHeartbeats 500000 in
theorem pointBlowupChartToStalk_source_order (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a)))
    (hp : affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (affineBlowUp.chart _ a p) = IsLocalRing.closedPoint (X.presheaf.stalk x))
    (r : X.presheaf.stalk x) :
    let q := pointBlowupLocalMap x (affineBlowUp.chart _ a p)
    localAdicOrder ((pointClosureIdeal x).blowUp.presheaf.stalk q)
      (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x
        (pointBlowupChart_image_over x a p hp) r) =
      localAdicOrder (Localization.AtPrime p.asIdeal)
        (algebraMap _ (Localization.AtPrime p.asIdeal)
          (algebraMap (X.presheaf.stalk x) (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (a : X.presheaf.stalk x)) r)) := by
  dsimp only
  let B : CommRingCat := (pointClosureIdeal x).blowUp.presheaf.stalk
    (pointBlowupLocalMap x (affineBlowUp.chart _ a p))
  obtain ⟨e, he⟩ := pointBlowupChartToStalk_exists_ringEquiv x a p
  calc
    localAdicOrder B (stalkMapAtEq _ _ x _ r) =
        localAdicOrder B (pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _ r)) :=
      congrArg (localAdicOrder B) (pointBlowupChartToStalk_algebraMap x a p hp r).symm
    _ = localAdicOrder (Localization.AtPrime p.asIdeal)
        (e (pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _ r))) :=
      (localAdicOrder_ringEquiv (R := B) (S := Localization.AtPrime p.asIdeal) e _).symm
    _ = _ := congrArg (localAdicOrder (Localization.AtPrime p.asIdeal)) (he _)

variable {K : Type u} [Field K] {n : ℕ} [IsIntegral X] [IsLocallyNoetherian X]

set_option maxHeartbeats 1000000 in
theorem pointBlowup_exists_exceptional_dvr_stalk (x : X)
    [Algebra K (X.presheaf.stalk x)]
    (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder (X.presheaf.stalk x) r)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i)))) (k : Fin n) :
    ∃ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x)
        (hB : IsDomain ((pointClosureIdeal x).blowUp.presheaf.stalk q)),
      @IsDiscreteValuationRing ((pointClosureIdeal x).blowUp.presheaf.stalk q) _ hB ∧
      ∀ (r : X.presheaf.stalk x) (d : ℕ), localAdicOrder (X.presheaf.stalk x) r = (d : ℕ∞) →
        localAdicOrder ((pointClosureIdeal x).blowUp.presheaf.stalk q)
          (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq r) = (d : ℕ∞) := by
  let R := X.presheaf.stalk x
  let A := affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k))
  have : IsDomain A := localPointBlowup_isDomain ψ T hX k
  have : IsNoetherianRing A := isNoetherianRing_affineBlowUpAlgebra _ _
  let a : IsLocalRing.maximalIdeal R := ⟨ψ (MvPolynomial.X k),
    localTaylorCoordinate_mem_maximalIdeal ψ T hX hord k⟩
  let p := localPointBlowupExceptionalPrime ψ T hX hord hmax k
  let L := Localization.AtPrime p.asIdeal
  have : IsDiscreteValuationRing L :=
    localPointBlowup_exceptional_isDiscreteValuationRing ψ T hX hord hmax k
  let q := pointBlowupLocalMap x (affineBlowUp.chart _ a p)
  have hp : affineBlowUp.π (IsLocalRing.maximalIdeal R) (affineBlowUp.chart _ a p) =
      IsLocalRing.closedPoint R := localPointBlowup_exceptionalPrime_over ψ T hX hord hmax k
  have hq : (pointClosureIdeal x).blowUpπ q = x := pointBlowupChart_image_over x a p hp
  let B : CommRingCat := (pointClosureIdeal x).blowUp.presheaf.stalk q
  obtain ⟨e, _⟩ := pointBlowupChartToStalk_exists_ringEquiv x a p
  obtain ⟨hB, hDVR⟩ := ringEquiv_dvr_structure (B := B) (L := L) e
  refine ⟨q, hq, hB, hDVR, ?_⟩
  intro r d hr
  exact (pointBlowupChartToStalk_source_order x a p hp r).trans
    (localPointBlowup_exact_exceptional_order ψ T hX hord hmax k r d hr)

end MixedFujita
