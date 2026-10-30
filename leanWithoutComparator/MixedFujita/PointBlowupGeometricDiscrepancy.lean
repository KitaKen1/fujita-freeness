/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupMatchedStalkCoordinates
public import MixedFujita.PointBlowupStalkCanonical
public import MixedFujita.PointBlowupSmoothBirational
public import MixedFujita.CartierPointBlowupExceptionalOrder

/-! Geometric discrepancy at the actual exceptional DVR of a point blow-up.
The adapted coordinates, chart equations, nonunit exceptional coordinate,
prime of codimension one and exact section orders are all constructed.
The global relative canonical divisor is the existing Cartier divisor.
No characteristic-zero or additional coordinate-comparison premise is used. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of K))] {Z : X.IdealSheafData} {x : X}
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 800000 in
theorem pointBlowup_matched_relativeCanonical_coefficient
    [IsIntegral Z.blowUp] [IsLocallyNoetherian Z.blowUp] [IsDominant Z.blowUpπ]
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n Z x) (hxZ : x ∈ Z.support) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
    ∀ (c₀ : EtaleChart K X n) (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
      (c'₀ : EtaleChart K Z.blowUp n) (hT : iSup (fun c : EtaleChart K Z.blowUp n => c.U) = ⊤)
      (hR : IsUnit (chartRelativeJacobianDet Z.blowUpπ c₀ c'₀))
      (t : CodimensionOnePoint Z.blowUp) [IsDiscreteValuationRing (Z.blowUp.presheaf.stalk (t : Z.blowUp))]
      (_ht : Z.blowUpπ (t : Z.blowUp) = x),
      cartierCoefficient (relativeCanonicalDivisor n Z.blowUpπ c₀ hX c'₀ hT hR) (t : Z.blowUp) =
        (n : ℤ) - 1 := by
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let : Z.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  dsimp only
  intro c₀ hX c'₀ hT hR t _ ht
  obtain ⟨k, τ, hτ, hk, hcoord⟩ := etalePointBlowup_matched_stalk_coordinates E hxZ (t : Z.blowUp) ht
  let c := etaleChartOfToAffineSpace E.U ⟨⟨x, E.mem⟩⟩ E.v E.etale
  have hc : Z.blowUpπ (t : Z.blowUp) ∈ c.U := ht.symm ▸ E.mem
  apply pointBlowup_stalk_relativeCanonical_coefficient Z.blowUpπ c₀ hX c'₀ hT hR t c hc τ hτ k hk
  intro i
  change Z.blowUpπ.stalkMap (t : Z.blowUp) (X.presheaf.germ E.U.1 _ hc
    (c.coords (MvPolynomial.X i))) = _
  rw [etaleChartOfToAffineSpace_coords]
  exact hcoord i

variable [IsAlgClosed K] [Smooth (X ↘ Spec (.of K))]

set_option maxHeartbeats 1000000 in
theorem smooth_closedPoint_pointBlowup_exists_dvr_orders_and_discrepancy
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X)) (k : Fin n) :
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
    let hdim : 0 < topologicalKrullDim X := hn.symm ▸ (by exact_mod_cast k.pos : (0 : WithBot ℕ∞) < n)
    let : IsIntegral (pointClosureIdeal x).blowUp := pointBlowup_isIntegral hdim x hx
    let : IsLocallyNoetherian (pointClosureIdeal x).blowUp :=
      Scheme.IdealSheafData.blowUp.isLocallyNoetherian (pointClosureIdeal x)
    let : IsDominant (pointClosureIdeal x).blowUpπ := pointBlowup_isDominant hdim x hx
    let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    let : (pointClosureIdeal x).blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
    let : SmoothOfRelativeDimension n (X ↘ Spec (.of K)) := geometricSmoothScheme_relativeDimension (K := K) n hn
    let : SmoothOfRelativeDimension n ((pointClosureIdeal x).blowUp ↘ Spec (.of K)) :=
      smooth_closedPoint_pointBlowup_smoothOfRelativeDimension hn x hx
    let hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (pointClosureIdeal x).blowUpπ) :=
      pointBlowup_functionField_bijective hdim x hx
    ∀ (c₀ : EtaleChart K X n) (c'₀ : EtaleChart K (pointClosureIdeal x).blowUp n),
    ∃ (t : CodimensionOnePoint (pointClosureIdeal x).blowUp)
      (ht : (pointClosureIdeal x).blowUpπ (t : (pointClosureIdeal x).blowUp) = x),
      IsDiscreteValuationRing ((pointClosureIdeal x).blowUp.presheaf.stalk (t : (pointClosureIdeal x).blowUp)) ∧
      cartierCoefficient (birationalRelativeCanonicalDivisor n (pointClosureIdeal x).blowUpπ hπ
        c₀ etaleCharts_cover c'₀ etaleCharts_cover) (t : (pointClosureIdeal x).blowUp) = (n : ℤ) - 1 ∧
      1 + cartierCoefficient (birationalRelativeCanonicalDivisor n (pointClosureIdeal x).blowUpπ hπ
        c₀ etaleCharts_cover c'₀ etaleCharts_cover) (t : (pointClosureIdeal x).blowUp) = (n : ℤ) ∧
      ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
        (s : Γ(D.sheaf, ⊤)) (d : ℕ), cartierSectionVanishingOrder D x s = (d : ℕ∞) →
        localAdicOrder ((pointClosureIdeal x).blowUp.presheaf.stalk (t : (pointClosureIdeal x).blowUp))
          (stalkMapAtEq (pointClosureIdeal x).blowUpπ (t : (pointClosureIdeal x).blowUp) x ht
            (cartierLocalCoefficient D x f hf s)) = (d : ℕ∞) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  have hdim : 0 < topologicalKrullDim X := hn.symm ▸ (by exact_mod_cast k.pos : (0 : WithBot ℕ∞) < n)
  let : IsIntegral (pointClosureIdeal x).blowUp := pointBlowup_isIntegral hdim x hx
  let : IsDominant (pointClosureIdeal x).blowUpπ := pointBlowup_isDominant hdim x hx
  let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
    ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let : (pointClosureIdeal x).blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (X ↘ Spec (.of K)) := geometricSmoothScheme_relativeDimension (K := K) n hn
  let : SmoothOfRelativeDimension n ((pointClosureIdeal x).blowUp ↘ Spec (.of K)) :=
    smooth_closedPoint_pointBlowup_smoothOfRelativeDimension hn x hx
  have : Smooth ((pointClosureIdeal x).blowUp ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  dsimp only
  intro c₀ c'₀
  have : IsLocallyNoetherian (pointClosureIdeal x).blowUp :=
    LocallyOfFiniteType.isLocallyNoetherian ((pointClosureIdeal x).blowUp ↘ Spec (.of K))
  obtain ⟨q, hq, hB, hDVR, horders⟩ :=
    smooth_closedPoint_exists_exceptional_dvr_with_section_orders (K := K) hn x hx k
  let := hB
  let := hDVR
  let t : CodimensionOnePoint (pointClosureIdeal x).blowUp := ⟨q, coheight_eq_one_of_stalk_DVR q⟩
  obtain ⟨E⟩ := smooth_closedPoint_exists_adaptedPointBlowupCoordinates (K := K) n hn x hx
  have hxZ : x ∈ (pointClosureIdeal x).support := by
    change x ∈ ((pointClosureIdeal x).support : Set X)
    rw [pointClosureIdeal_support_closedPoint x hx]
    exact Set.mem_singleton x
  have hc : cartierCoefficient (birationalRelativeCanonicalDivisor n (pointClosureIdeal x).blowUpπ
      (pointBlowup_functionField_bijective (hn.symm ▸ (by exact_mod_cast k.pos : (0 : WithBot ℕ∞) < n)) x hx)
      c₀ etaleCharts_cover c'₀ etaleCharts_cover) q = (n : ℤ) - 1 :=
    pointBlowup_matched_relativeCanonical_coefficient E hxZ c₀ etaleCharts_cover c'₀ etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective _
        (pointBlowup_functionField_bijective hdim x hx) c₀ c'₀) t hq
  exact ⟨t, hq, hDVR, hc, by rw [hc]; ring, horders⟩

end MixedFujita
