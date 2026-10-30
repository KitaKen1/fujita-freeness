/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupLocalBaseChange
public import Hironaka.Scheme.BlowUp.Cancellation
public import Hironaka.Scheme.IdealSheaf.StalkIdeal
public import Hironaka.Scheme.BlowUp.Glue.Global

/-!
Actual chart maps into the stalks of the original scheme point blow-up.
The maps agree with the actual projection on every source germ. The actual exceptional
stalk ideal is principal with the transported equation. Every point over the centre is
represented on a chart from any family generating the maximal ideal.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}}

theorem pointBlowupChart_image_over (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a)))
    (hp : affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p) =
        IsLocalRing.closedPoint (X.presheaf.stalk x)) :
    (pointClosureIdeal x).blowUpπ (pointBlowupLocalMap x
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p)) = x := by
  change (pointBlowupLocalMap x ≫ (pointClosureIdeal x).blowUpπ) _ = x
  rw [(pointBlowupLocalMap_isPullback x).w]
  change X.fromSpecStalk x (affineBlowUp.π _ _) = x
  exact (congrArg (X.fromSpecStalk x) hp).trans
    (Scheme.fromSpecStalk_closedPoint (X := X) (x := x))

theorem pointBlowupChartToStalk_germ (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a)))
    (hp : affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p) =
        IsLocalRing.closedPoint (X.presheaf.stalk x))
    (V : X.Opens) (hxV : x ∈ V) (s : Γ(X, V)) :
    pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _
      (X.presheaf.germ V x hxV s)) =
    (pointClosureIdeal x).blowUpπ.stalkMap (pointBlowupLocalMap x
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p))
      (X.presheaf.germ V _ ((pointBlowupChart_image_over x a p hp).symm ▸ hxV) s) := by
  let q := affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p
  let e := pointBlowupLocalStalkIso x q
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  change e.hom (e.inv (affineBlowupChartToStalk _ a p (algebraMap (X.presheaf.stalk x) _
      (X.presheaf.germ V x hxV s)))) = _
  rw [Iso.inv_hom_id_apply]
  have hV : (pointClosureIdeal x).blowUpπ (pointBlowupLocalMap x q) ∈ V :=
    (pointBlowupChart_image_over x a p hp).symm ▸ hxV
  have h1 : (pointBlowupLocalMap x).stalkMap q
      ((pointClosureIdeal x).blowUpπ.stalkMap (pointBlowupLocalMap x q)
        (X.presheaf.germ V _ hV s)) =
      (pointBlowupLocalMap x ≫ (pointClosureIdeal x).blowUpπ).stalkMap q
        (X.presheaf.germ V _ hV s) := by
    rw [Scheme.Hom.stalkMap_comp]
    rfl
  have hg := stalkMap_germ_eq_of_eq_comp_fromSpecStalk x
    (pointBlowupLocalMap x ≫ (pointClosureIdeal x).blowUpπ)
    (pointBlowupLocalMap_isPullback x).w q V hxV hV s
  exact (affineBlowupChartToStalk_algebraMap _ a p (X.presheaf.germ V x hxV s)).trans
    (h1.trans hg).symm

theorem pointBlowupChartToStalk_algebraMap (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a)))
    (hp : affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p) =
        IsLocalRing.closedPoint (X.presheaf.stalk x)) (r : X.presheaf.stalk x) :
    pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _ r) =
      stalkMapAtEq (pointClosureIdeal x).blowUpπ
        (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p))
        x (pointBlowupChart_image_over x a p hp) r := by
  obtain ⟨V, hxV, s, rfl⟩ := X.presheaf.exists_germ_eq r
  rw [stalkMapAtEq_germ]
  exact pointBlowupChartToStalk_germ x a p hp V hxV s

theorem pointBlowupChartToStalk_exceptionalIdeal (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a))) :
    ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal
        (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p)) =
      Ideal.span {pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _ a)} := by
  let q := affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p
  let e := pointBlowupLocalStalkIso x q
  have h : (((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal
      (pointBlowupLocalMap x q)).map e.hom.hom =
        Ideal.span {affineBlowupChartToStalk _ a p (algebraMap (X.presheaf.stalk x) _ a)} := by
    calc
      _ = (((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).comap
          (pointBlowupLocalMap x)).stalkIdeal q :=
        (Scheme.IdealSheafData.stalkIdeal_comap _ _ _).symm
      _ = _ := by rw [pointBlowupLocalMap_exceptionalIdeal, affineBlowupChartToStalk_exceptionalIdeal]
  have he := congrArg (Ideal.map e.inv.hom) h
  have hid : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
    ext r
    exact Iso.hom_inv_id_apply e r
  change _ = Ideal.span {e.inv.hom (affineBlowupChartToStalk _ a p (algebraMap (X.presheaf.stalk x) _ a))}
  simpa only [Ideal.map_map, hid, Ideal.map_id, Ideal.map_span, Set.image_singleton] using he

theorem pointBlowupChartToStalk_exceptional_nonZeroDivisor (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a))) :
    pointBlowupChartToStalk x a p (algebraMap (X.presheaf.stalk x) _ a) ∈
      nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk
        (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p))) := by
  have hInv := Scheme.IdealSheafData.blowUp.isInvertible_comap_π (pointClosureIdeal x)
  obtain ⟨g, hg, hgen⟩ := hInv.exists_mem_nonZeroDivisors_stalkIdeal_eq_span
    (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p))
  exact mem_nonZeroDivisors_of_span_eq_span hg
    ((pointBlowupChartToStalk_exceptionalIdeal x a p).symm.trans hgen)

theorem pointBlowupLocalMap_exists_chart_over (x : X) {ι : Type*}
    (y : ι → X.presheaf.stalk x)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    ∃ (i : ι) (hi : y i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (y i)))),
      pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ⟨y i, hi⟩ p) = q ∧
      affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ⟨y i, hi⟩ p) =
          IsLocalRing.closedPoint (X.presheaf.stalk x) := by
  have hqx : (pointClosureIdeal x).blowUpπ q = X.fromSpecStalk x (IsLocalRing.closedPoint _) := by
    rw [hq, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨q', hφ, hπ⟩ := Scheme.exists_preimage_of_isPullback (pointBlowupLocalMap_isPullback x)
    q (IsLocalRing.closedPoint _) hqx
  obtain ⟨⟨a, hay⟩, hchart⟩ := affineBlowUp.exists_mem_opensRange_chart_of_span_eq
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (Set.range y) hmax.symm q'
  obtain ⟨i, rfl⟩ := hay
  have hi : y i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hmax]
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨p, hp⟩ := hchart
  exact ⟨i, hi, p, (congrArg (pointBlowupLocalMap x) hp).trans hφ,
    (congrArg (affineBlowUp.π _) hp).trans hπ⟩

end MixedFujita
