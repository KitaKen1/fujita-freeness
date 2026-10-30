/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.SmoothStalkNormality
public import Hironaka.Scheme.BlowUpSequence.CompositeBlowUp

/-! Principalize the actual ideal while retaining a blow-up sequence,
center avoidance and SNC support. This retained sequence is the input to the
existing compatible-source lift, avoiding a new resolution-of-maps theorem. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {k : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsRegular Y] [IsNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of K))]

/-- A prescribed bad locus has a smooth projective birational SNC base model. -/
theorem exists_principalizing_smooth_snc_base_sequence (cY : EtaleChart K Y k) (Z : Closeds Y)
    (hZη : genericPoint Y ∉ (Z : Set Y)) (I : Y.IdealSheafData)
    (hIZ : (I.support : Set Y) ⊆ (Z : Set Y)) :
    ∃ S : Scheme.BlowUpSequence Y,
      (∀ (i : Fin S.length) (z : S.stage i.castSucc), z ∈ (S.center i).support →
        S.stageMap i.castSucc z ∈ (Z : Set Y)) ∧
      ∃ (_ : IsIntegral S.last) (_ : S.last.Over (Spec (CommRingCat.of K)))
        (_ : IsNoetherian S.last)
        (_ : SmoothOfRelativeDimension k (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsDominant S.composite) (_ : S.composite.IsOver (Spec (CommRingCat.of K)))
        (_ : IsProper S.composite) (_ : IsProjective S.composite)
        (_ : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)))
        (_ : QuasiCompact (S.last ↘ Spec (CommRingCat.of K)))
        (_ : IsSeparated (S.last ↘ Spec (CommRingCat.of K)))
        (cB : EtaleChart K S.last k),
        Function.Bijective (dominantFunctionFieldAlgHom (K := K) S.composite) ∧
        IsIso (S.composite ∣_ Z.compl) ∧
        ∃ (r : ℕ) (ξ : Fin r → S.last), Function.Injective ξ ∧
          (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K k ξ ∧
          (∀ β : CodimensionOnePoint S.last, (β : S.last) ∉ Set.range ξ →
            S.composite (β : S.last) ∉ (Z : Set Y)) ∧ (I.comap S.composite).IsInvertible := by
  classical
  obtain ⟨S, hc, hreg, hInv, E, hEsnc, hEsupp⟩ :=
    exists_blowUpSequence_isSncBoundary_isInvertible_comap (K := K) Y Z hZη I hIZ
  have hBi : IsIntegral S.last := blowUpSequence_isIntegral_last_of_centers_over S Z hc hZη
  let instB : S.last.Over (Spec (CommRingCat.of K)) :=
    ⟨S.composite ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have hρover : S.composite.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hρprop : IsProper S.composite := S.isProper_composite
  have hρproj : IsProjective S.composite := S.isProjective_composite
  have hρdom : IsDominant S.composite := blowUpSequence_isDominant_of_centers_over S Z hc hZη
  have hBft : LocallyOfFiniteType (S.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (S.composite ≫ (Y ↘ Spec (CommRingCat.of K))))
  have hBqc : QuasiCompact (S.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (QuasiCompact (S.composite ≫ (Y ↘ Spec (CommRingCat.of K))))
  have hBsep : IsSeparated (S.last ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (IsSeparated (S.composite ≫ (Y ↘ Spec (CommRingCat.of K))))
  have hBN : IsLocallyNoetherian S.last := LocallyOfFiniteType.isLocallyNoetherian S.composite
  have hBc : CompactSpace S.last := QuasiCompact.compactSpace_of_compactSpace S.composite
  have hBnoeth : IsNoetherian S.last := { toIsLocallyNoetherian := hBN, toCompactSpace := hBc }
  have hBsm : SmoothOfRelativeDimension k (S.last ↘ Spec (CommRingCat.of K)) :=
    blowUpSequence_smoothOfRelativeDimension_of_centers_over S Z hc hZη hreg cY
  have hbir : Function.Bijective (dominantFunctionFieldAlgHom (K := K) S.composite) :=
    dominantFunctionFieldMap_bijective_of_isIso_stalkMap S.composite
      (blowUpSequence_isIso_stalkMap_of_centers_over S Z hc (genericPoint S.last)
        (by rw [dominant_map_genericPoint]; exact hZη))
  have hiso : IsIso (S.composite ∣_ Z.compl) :=
    Hironaka.Sequence.isIso_composite_restrict_of_centers_disjoint S Z.compl fun i =>
      Set.disjoint_left.mpr fun z hz hzU => hzU (hc i z hz)
  obtain ⟨b⟩ : Nonempty S.last := inferInstance
  obtain ⟨cB, -⟩ := Opens.mem_iSup.mp
    ((etaleCharts_cover (K := K) (X := S.last) (n := k)).symm ▸ Opens.mem_top b)
  let e : Fin (Nat.card E.support.genericPoints) ≃ E.support.genericPoints :=
    (Finite.equivFin _).symm
  let ξ : Fin (Nat.card E.support.genericPoints) → S.last := fun i => (e i).1
  have hinj : Function.Injective ξ := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, ξ i ∈ E.support.genericPoints := fun i => (e i).2
  have hcoh : ∀ η ∈ E.support.genericPoints, Order.coheight η = 1 := fun η hη =>
    coheight_eq_one_of_mem_genericPoints_of_isSncBoundary E hEsnc hη
  have hsnc : IsSNCFamily K k ξ := isSNCFamily_of_isSncBoundary E hEsnc ξ hinj hmem
  refine ⟨S, hc, hBi, instB, hBnoeth, hBsm, hρdom, hρover, hρprop, hρproj,
    hBft, hBqc, hBsep, cB, hbir, hiso, _, ξ, hinj, fun i => hcoh _ (hmem i), hsnc, ?_, hInv⟩
  intro β hβ hbad
  have hβE : (β : S.last) ∈ E.support := by
    change (β : S.last) ∈ (E.support : Set S.last)
    rw [hEsupp]
    exact hbad
  obtain ⟨η, hη, hηβ⟩ := Closeds.exists_mem_genericPoints_specializes E.support hβE
  have heq : (⟨η, hcoh η hη⟩ : CodimensionOnePoint S.last) = β :=
    CodimensionOnePoint.eq_of_specializes (x := β) (y := ⟨η, hcoh η hη⟩) hηβ
  apply hβ
  refine ⟨e.symm ⟨η, hη⟩, ?_⟩
  change ((e (e.symm ⟨η, hη⟩)).1 : S.last) = (β : S.last)
  rw [Equiv.apply_symm_apply]
  exact congrArg Subtype.val heq

end MixedFujita

