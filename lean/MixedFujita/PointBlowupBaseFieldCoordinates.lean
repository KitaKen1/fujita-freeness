/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupEtaleStalkCoordinates
public import MixedFujita.CanonicalDivisor

/-! Compatibility with the actual scheme base-field action. The constructed
coordinates on every actual exceptional stalk are K-algebra maps for the
projection-induced structure morphism by the actual blow-up projection. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite Scheme.Hom
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

noncomputable def polynomialSectionsAlgHom {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    (σ : Y ⟶ Spec (.of (MvPolynomial (Fin n) K)))
    (hbase : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) =
      (Y ↘ Spec (.of K))) (V : Y.Opens) : MvPolynomial (Fin n) K →ₐ[K] Γ(Y, V) where
  toRingHom := sectionsHom σ V
  commutes' c := by
    change sectionsHom σ V (MvPolynomial.C c) =
      ((Y.baseRingToStructurePresheaf K).app (op V)) c
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    change sectionsHom σ V (MvPolynomial.C c) = sectionsHom (Y ↘ Spec (.of K)) V c
    rw [← hbase, sectionsHom_comp_specMap]
    rfl

theorem polynomialSectionsAlgHom_formallyEtale {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    (σ : Y ⟶ Spec (.of (MvPolynomial (Fin n) K))) [Etale σ]
    (hbase : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) =
      (Y ↘ Spec (.of K))) (V : Y.affineOpens) :
    (polynomialSectionsAlgHom σ hbase V.1).toRingHom.FormallyEtale :=
  sectionsHom_formallyEtale_of_etale σ V

noncomputable def polynomialStalkAlgHom {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    (σ : Y ⟶ Spec (.of (MvPolynomial (Fin n) K)))
    (hbase : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) =
      (Y ↘ Spec (.of K))) (V : Y.affineOpens) (p : Y) (hp : p ∈ V.1) :
    MvPolynomial (Fin n) K →ₐ[K] Y.presheaf.stalk p :=
  (sectionStalkAlgHom V.1 p hp).comp (polynomialSectionsAlgHom σ hbase V.1)

theorem polynomialStalkAlgHom_formallyEtale {Y : Scheme.{u}} [Y.Over (Spec (.of K))]
    (σ : Y ⟶ Spec (.of (MvPolynomial (Fin n) K))) [Etale σ]
    (hbase : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) =
      (Y ↘ Spec (.of K))) (V : Y.affineOpens) (p : Y) (hp : p ∈ V.1) :
    (polynomialStalkAlgHom σ hbase V p hp).toRingHom.FormallyEtale :=
  etalePolynomial_stalkMap_formallyEtale σ V p hp

variable {X : Scheme.{u}} [X.Over (Spec (.of K))] {Z : X.IdealSheafData} {x : X}

theorem etalePointBlowupChartToGlobal_comp_base
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n Z x) (k : Fin n) :
    etalePointBlowupChartToGlobal E k ≫ Z.blowUpπ ≫ (X ↘ Spec (.of K)) =
      pullback.snd (etalePointBlowupModelMap E)
        (CoordinateSubspace.modelChart K n n k k.isLt) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K))) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))
  have hscalar : Spec.map (CommRingCat.ofHom (polynomialPointBlowupMap (K := K) k).toRingHom) ≫
      c = c := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (polynomialPointBlowupMap (K := K) k).comp_algebraMap
  have h := congrArg (fun g => g ≫ c) (etalePointBlowupChart_projection E k)
  simp only [Category.assoc, hscalar] at h
  dsimp only [c] at h
  rw [toAffineSpace_comp_structure] at h
  rw [etalePointBlowupChartToGlobal, Category.assoc, blowUpMap_π_assoc]
  exact h

set_option maxHeartbeats 800000 in
theorem etalePointBlowup_actual_stalk_baseField_coordinates
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n Z x)
    (q : Z.blowUp) (hq : Z.blowUpπ q = x) :
    let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ τ : MvPolynomial (Fin n) K →ₐ[K] Z.blowUp.presheaf.stalk q,
      τ.toRingHom.FormallyEtale := by
  let : Z.blowUp.Over (Spec (.of K)) := ⟨Z.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  obtain ⟨k, p, rfl⟩ := etalePointBlowupChartToGlobal_covers_fibre E q hq
  let Y := etalePointBlowupChart E k
  let σ := pullback.snd (etalePointBlowupModelMap E)
    (CoordinateSubspace.modelChart K n n k k.isLt)
  let : Y.Over (Spec (.of K)) :=
    ⟨σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin n) K)))⟩
  let ρ := etalePointBlowupChartToGlobal E k
  have : ρ.IsOver (Spec (.of K)) := ⟨etalePointBlowupChartToGlobal_comp_base E k⟩
  obtain ⟨V, hp⟩ := Scheme.IdealSheafData.exists_affineOpens_mem p
  let τ := polynomialStalkAlgHom σ rfl V p hp
  let e := AlgEquiv.ofBijective (schemeStalkMapAlgHom (K := K) ρ p)
    (ConcreteCategory.bijective_of_isIso (ρ.stalkMap p))
  refine ⟨e.symm.toAlgHom.comp τ, RingHom.FormallyEtale.comp
    (polynomialStalkAlgHom_formallyEtale σ rfl V p hp) ?_⟩
  exact ringHom_formallyEtale_of_etale e.symm.toRingEquiv.toRingHom
    (RingHom.Etale.of_bijective e.symm.bijective)

theorem smooth_closedPoint_pointBlowup_all_stalks_baseField_coordinates
    [IsAlgClosed K] [IsIntegral X] [Smooth (X ↘ Spec (.of K))]
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q,
      τ.toRingHom.FormallyEtale := by
  let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
    ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
  obtain ⟨E⟩ := smooth_closedPoint_exists_adaptedPointBlowupCoordinates (K := K) n hn x hx
  exact etalePointBlowup_actual_stalk_baseField_coordinates E q hq

theorem smooth_closedPoint_pointBlowup_all_stalks_differential_basis
    [IsAlgClosed K] [IsIntegral X] [Smooth (X ↘ Spec (.of K))]
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    letI : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q)
      (b : Module.Basis (Fin n) ((pointClosureIdeal x).blowUp.presheaf.stalk q)
        Ω[((pointClosureIdeal x).blowUp.presheaf.stalk q)⁄K]),
      ∀ i, b i = KaehlerDifferential.D K ((pointClosureIdeal x).blowUp.presheaf.stalk q)
        (τ (MvPolynomial.X i)) := by
  let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
    ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
  obtain ⟨τ, hτ⟩ := smooth_closedPoint_pointBlowup_all_stalks_baseField_coordinates (K := K) hn x hx q hq
  exact ⟨τ, etaleCoordinateBasis τ hτ, etaleCoordinateBasis_apply τ hτ⟩

end MixedFujita
