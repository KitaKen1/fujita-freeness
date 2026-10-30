/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StandardPointBlowupExceptionalRestriction
public import Hironaka.Scheme.Smooth.BlowUpSmoothChart
public import Hironaka.Scheme.Smooth.EtaleCoordinatesAdapted
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Actual blow-up charts over an adapted étale neighbourhood with zero-dimensional centre.
The charts are base changes of the standard point-blow-up charts. They cover the local
blow-up, are open immersions into it and étale over affine space, and their exceptional
ideal is the inverse image of (X_k). No identification with a supplied completion coordinate
system, exceptional valuation, or discrepancy is asserted here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} {n : ℕ}
  {f : X ⟶ Spec (.of K)} {Z : X.IdealSheafData} {x : X}

theorem exists_etalePointBlowup_modelMap (E : EtaleCoordinatesAdapted f n n Z x) :
    ∃ φ : Scheme.IdealSheafData.blowUp (Z.comap E.U.1.ι) ⟶
        CoordinateSubspace.modelBlowUp K n n,
      IsPullback φ (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))
        (affineBlowUp.π (CoordinateSubspace.centerIdeal K n n))
        (toAffineSpace f E.U.1 E.v) ∧ Etale φ := by
  obtain ⟨e, he⟩ := exists_iso_blowUp_coordinateSubspace K n n
  obtain ⟨φ, H⟩ := exists_isPullback_blowUp E
  have : Etale φ := etale_of_isPullback_blowUp E H
  refine ⟨φ ≫ e.hom, ?_, inferInstance⟩
  exact H.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using he.symm) (by simp)

/-- The actual local blow-up map to the standard affine model. -/
noncomputable def etalePointBlowupModelMap (E : EtaleCoordinatesAdapted f n n Z x) :=
  (exists_etalePointBlowup_modelMap E).choose

theorem etalePointBlowupModelMap_isPullback (E : EtaleCoordinatesAdapted f n n Z x) :
    IsPullback (etalePointBlowupModelMap E)
      (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))
      (affineBlowUp.π (CoordinateSubspace.centerIdeal K n n))
      (toAffineSpace f E.U.1 E.v) :=
  (exists_etalePointBlowup_modelMap E).choose_spec.1

instance etalePointBlowupModelMap_etale (E : EtaleCoordinatesAdapted f n n Z x) :
    Etale (etalePointBlowupModelMap E) :=
  (exists_etalePointBlowup_modelMap E).choose_spec.2

/-- An actual open chart of the local blow-up, étale over the standard affine chart. -/
@[reducible]
noncomputable def etalePointBlowupChart (E : EtaleCoordinatesAdapted f n n Z x) (k : Fin n) :
    Scheme.{u} :=
  pullback (etalePointBlowupModelMap E) (CoordinateSubspace.modelChart K n n k k.isLt)

instance etalePointBlowupChart_openImmersion (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) : IsOpenImmersion
      (pullback.fst (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt)) := inferInstance

instance etalePointBlowupChart_etale (E : EtaleCoordinatesAdapted f n n Z x) (k : Fin n) :
    Etale (pullback.snd (etalePointBlowupModelMap E)
      (CoordinateSubspace.modelChart K n n k k.isLt)) := inferInstance

theorem etalePointBlowupChart_projection (E : EtaleCoordinatesAdapted f n n Z x) (k : Fin n) :
    pullback.fst (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt) ≫
      Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι) ≫ toAffineSpace f E.U.1 E.v =
    pullback.snd (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt) ≫
      Spec.map (CommRingCat.ofHom (polynomialPointBlowupMap (K := K) k).toRingHom) := by
  rw [← (etalePointBlowupModelMap_isPullback E).w,
    ← Category.assoc, pullback.condition, Category.assoc,
    standardPointBlowup_chart_projection]

theorem etalePointBlowupChart_exists_preimage (E : EtaleCoordinatesAdapted f n n Z x)
    (q : Scheme.IdealSheafData.blowUp (Z.comap E.U.1.ι)) :
    ∃ (k : Fin n) (p : etalePointBlowupChart E k),
      pullback.fst (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt) p = q := by
  have h : etalePointBlowupModelMap E q ∈
      ⨆ (k : Fin n) (hk : k.val < n),
        (CoordinateSubspace.modelChart K n n k hk).opensRange := by
    rw [CoordinateSubspace.iSup_opensRange_modelChart]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  obtain ⟨hk, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp hk
  obtain ⟨z, hz⟩ := Scheme.Hom.mem_opensRange.mp hq
  obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (etalePointBlowupModelMap E)
      (CoordinateSubspace.modelChart K n n k k.isLt)) q z hz.symm
  exact ⟨k, p, hp⟩

theorem etalePointBlowup_exceptionalIdeal (E : EtaleCoordinatesAdapted f n n Z x) :
    (Z.comap E.U.1.ι).comap (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι)) =
      (affineBlowUp.exceptionalIdeal (CoordinateSubspace.centerIdeal K n n)).comap
        (etalePointBlowupModelMap E) := by
  calc
    _ = ((coordinateSubspace K n n).comap (toAffineSpace f E.U.1 E.v)).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι)) :=
      congrArg (fun J => J.comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))) E.adapted
    _ = _ := by
      rw [← Scheme.IdealSheafData.comap_comp,
    ← (etalePointBlowupModelMap_isPullback E).w, Scheme.IdealSheafData.comap_comp]
      rfl

theorem etalePointBlowupChart_exceptionalIdeal (E : EtaleCoordinatesAdapted f n n Z x)
    (k : Fin n) :
    ((Z.comap E.U.1.ι).comap
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))).comap
      (pullback.fst (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt)) =
    (Scheme.IdealSheafData.ofIdealTop
      ((Ideal.span {(MvPolynomial.X k : MvPolynomial (Fin n) K)}).map
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) K))).inv.hom)).comap
      (pullback.snd (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt)) := by
  rw [etalePointBlowup_exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
    pullback.condition, Scheme.IdealSheafData.comap_comp,
    standardPointBlowup_exceptional_ideal_chart]

theorem exists_etalePointBlowup_adaptedModel [PerfectField K]
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension 0 (Z.subschemeι ≫ f)]
    (hxZ : x ∈ Z.support) (hx : IsClosed ({x} : Set X)) :
    ∃ E : EtaleCoordinatesAdapted f n n Z x,
      IsPullback (etalePointBlowupModelMap E)
        (Scheme.IdealSheafData.blowUpπ (Z.comap E.U.1.ι))
        (affineBlowUp.π (CoordinateSubspace.centerIdeal K n n))
        (toAffineSpace f E.U.1 E.v) ∧ Etale (etalePointBlowupModelMap E) := by
  have : SmoothOfRelativeDimension (n - n) (Z.subschemeι ≫ f) := by simpa
  obtain ⟨E⟩ := nonempty_etaleCoordinatesAdapted f n n Z le_rfl hxZ hx
  exact ⟨E, etalePointBlowupModelMap_isPullback E, inferInstance⟩

end MixedFujita
