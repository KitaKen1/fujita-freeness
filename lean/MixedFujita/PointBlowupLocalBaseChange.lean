/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointClosureSubscheme
public import MixedFujita.LocalPointBlowupStalkRestriction
public import Hironaka.Scheme.Smooth.LocalBlowUp
public import Hironaka.Scheme.Smooth.LocalBlowUpStalk
public import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints

/-!
The actual reduced point centre and the base change of its scheme blow-up to the local ring.
At a closed point the centre is exactly that point. The centre's stalk is the maximal ideal,
and the local blow-up map induces actual stalk isomorphisms. Its inverse transports the
actual chart algebra to the stalk of the original scheme's blow-up.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}}

theorem pointClosureIdeal_stalkIdeal_self (x : X) :
    (pointClosureIdeal x).stalkIdeal x = IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  Hironaka.BMO.stalkIdeal_vanishingIdeal_closure_self x

theorem pointClosureIdeal_support_closedPoint (x : X) (hx : IsClosed ({x} : Set X)) :
    ((pointClosureIdeal x).support : Set X) = {x} := by
  rw [← Scheme.IdealSheafData.range_subschemeι, range_pointClosureι, hx.closure_eq]

theorem exists_pointBlowupLocalMap (x : X) :
    ∃ φ : affineBlowUp (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ⟶
        (pointClosureIdeal x).blowUp,
      IsPullback φ (affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
        (pointClosureIdeal x).blowUpπ (X.fromSpecStalk x) := by
  have h := exists_isPullback_fromSpecStalk (pointClosureIdeal x) x
  rw [pointClosureIdeal_stalkIdeal_self x] at h
  exact h

noncomputable def pointBlowupLocalMap (x : X) := (exists_pointBlowupLocalMap x).choose

theorem pointBlowupLocalMap_isPullback (x : X) :
    IsPullback (pointBlowupLocalMap x)
      (affineBlowUp.π (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
      (pointClosureIdeal x).blowUpπ (X.fromSpecStalk x) :=
  (exists_pointBlowupLocalMap x).choose_spec

noncomputable def pointBlowupLocalStalkIso (x : X)
    (q : affineBlowUp (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) :
    (pointClosureIdeal x).blowUp.presheaf.stalk (pointBlowupLocalMap x q) ≅
      (affineBlowUp (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).presheaf.stalk q := by
  have := isIso_stalkMap_of_isPullback_fromSpecStalk (pointBlowupLocalMap_isPullback x) q
  exact asIso ((pointBlowupLocalMap x).stalkMap q)

theorem pointBlowupLocalStalkIso_hom (x : X)
    (q : affineBlowUp (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) :
    (pointBlowupLocalStalkIso x q).hom = (pointBlowupLocalMap x).stalkMap q := rfl

theorem pointBlowupLocalMap_exceptionalIdeal (x : X) :
    ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).comap (pointBlowupLocalMap x) =
      affineBlowUp.exceptionalIdeal (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
  rw [← Scheme.IdealSheafData.comap_comp, (pointBlowupLocalMap_isPullback x).w,
    Scheme.IdealSheafData.comap_comp, comap_fromSpecStalk_eq_specIdealSheaf,
    pointClosureIdeal_stalkIdeal_self]
  rfl

noncomputable def pointBlowupChartToStalk (x : X)
    (a : IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a))) :
    affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a →+*
      (pointClosureIdeal x).blowUp.presheaf.stalk
        (pointBlowupLocalMap x (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p)) :=
  (pointBlowupLocalStalkIso x
      (affineBlowUp.chart (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p)).inv.hom.comp
    (affineBlowupChartToStalk (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) a p)

/-- The actual stalk map with its source point identified by an equality. -/
noncomputable def stalkMapAtEq {Y : Scheme.{u}} (ρ : Y ⟶ X) (q : Y) (x : X) (hq : ρ q = x) :
    X.presheaf.stalk x →+* Y.presheaf.stalk q := by
  subst x
  exact (ρ.stalkMap q).hom

theorem stalkMapAtEq_germ {Y : Scheme.{u}} (ρ : Y ⟶ X) (q : Y) (x : X) (hq : ρ q = x)
    (V : X.Opens) (hxV : x ∈ V) (s : Γ(X, V)) :
    stalkMapAtEq ρ q x hq (X.presheaf.germ V x hxV s) =
      ρ.stalkMap q (X.presheaf.germ V (ρ q) (hq.symm ▸ hxV) s) := by
  subst x
  rfl

end MixedFujita
