/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtalePointBlowupDifferentials
public import MixedFujita.PointBlowupAdaptedCoordinates
public import Hironaka.Scheme.BlowUp.BlowUpMap
public import Hironaka.Scheme.BlowUp.InvertibleSheaf

/-! Actual formally étale polynomial coordinates at every point of the original
point-blow-up fibre. The local base-change charts map by open immersions into
the original blow-up, so their actual differential bases transport to its stalks.
No rationality or closedness is required of the point in the exceptional fibre. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme.Hom
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {n : ℕ}
  {f : X ⟶ Spec (.of K)} {Z : X.IdealSheafData} {x : X}

noncomputable def etalePointBlowupChartToGlobal (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) : etalePointBlowupChart E k ⟶ Z.blowUp :=
  pullback.fst (etalePointBlowupModelMap E)
    (CoordinateSubspace.modelChart K n n k k.isLt) ≫ blowUpMap E.U.1.ι Z

instance etalePointBlowupChartToGlobal_openImmersion (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) : IsOpenImmersion (etalePointBlowupChartToGlobal E k) := by
  have : IsOpenImmersion (blowUpMap E.U.1.ι Z) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_blowUpMap E.U.1.ι Z).flip inferInstance
  unfold etalePointBlowupChartToGlobal
  infer_instance

theorem etalePointBlowupChartToGlobal_covers_fibre (E : EtaleCoordinatesAdapted f n n Z x)
    (q : Z.blowUp) (hq : Z.blowUpπ q = x) :
    ∃ (k : Fin n) (p : etalePointBlowupChart E k), etalePointBlowupChartToGlobal E k p = q := by
  obtain ⟨qU, hqU, -⟩ := Scheme.exists_preimage_of_isPullback
    (isPullback_blowUpMap E.U.1.ι Z) q (⟨x, E.mem⟩ : E.U.1) hq
  obtain ⟨k, p, hp⟩ := etalePointBlowupChart_exists_preimage E qU
  exact ⟨k, p, (congrArg (blowUpMap E.U.1.ι Z) hp).trans hqU⟩

theorem etalePointBlowup_actual_stalk_formallyEtale_coordinates
    (E : EtaleCoordinatesAdapted f n n Z x) (q : Z.blowUp) (hq : Z.blowUpπ q = x) :
    ∃ τ : MvPolynomial (Fin n) K →+* Z.blowUp.presheaf.stalk q, τ.FormallyEtale := by
  obtain ⟨k, p, rfl⟩ := etalePointBlowupChartToGlobal_covers_fibre E q hq
  obtain ⟨V, hp⟩ := Scheme.IdealSheafData.exists_affineOpens_mem p
  let e := asIso ((etalePointBlowupChartToGlobal E k).stalkMap p)
  let τ := e.inv.hom.comp (etalePointBlowupStalkCoords E k V p hp)
  refine ⟨τ, RingHom.FormallyEtale.comp
    (etalePointBlowupStalkCoords_formallyEtale E k V p hp) ?_⟩
  exact ringHom_formallyEtale_of_etale e.inv.hom
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso e.inv))

theorem smooth_closedPoint_pointBlowup_all_stalks_formallyEtale_coordinates
    [IsAlgClosed K] [IsIntegral X] [X.Over (Spec (.of K))]
    [Smooth (X ↘ Spec (.of K))] (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X)) (q : (pointClosureIdeal x).blowUp)
    (hq : (pointClosureIdeal x).blowUpπ q = x) :
    ∃ τ : MvPolynomial (Fin n) K →+* (pointClosureIdeal x).blowUp.presheaf.stalk q,
      τ.FormallyEtale := by
  obtain ⟨E⟩ := smooth_closedPoint_exists_adaptedPointBlowupCoordinates (K := K) n hn x hx
  exact etalePointBlowup_actual_stalk_formallyEtale_coordinates E q hq

end MixedFujita
