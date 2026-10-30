/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericSmoothBaseOpen
public import Hironaka.Scheme.Snc.HasSncWith
public import Hironaka.Scheme.IdealSheaf.StalkLe
public import Hironaka.Scheme.IdealSheaf.Order.Basic

/-!
Actual closed intersections of SNC components are coordinate subspaces in the
original stalks, hence regular. All the finitely many such strata, including
the empty intersection, become smooth over one actual nonempty base open under
a proper morphism. The common open is constructed, not supplied as a witness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual closed intersection of a chosen subset of the SNC components. -/
noncomputable def sncStratumIdeal {T : Scheme.{u}} (E : Scheme.DivisorFamily T)
    (s : Finset E.ι) : T.IdealSheafData := ⨆ i ∈ s, E.component i

/-- Every closed SNC stratum is cut out by a subset of the actual regular parameters. -/
theorem sncStratumIdeal_hasSncWith {T : Scheme.{u}} (E : Scheme.DivisorFamily T)
    (hE : E.IsSnc) (s : Finset E.ι) : E.HasSncWith (sncStratumIdeal E s) := by
  classical
  intro x hx
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := hE.2 x
  have hix (i : E.ι) (hi : i ∈ s) : x ∈ (E.component i).support := by
    apply (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mpr
    have hle : (E.component i).stalkIdeal x ≤ (sncStratumIdeal E s).stalkIdeal x := by
      rw [sncStratumIdeal, Scheme.IdealSheafData.stalkIdeal_iSup']
      exact le_iSup_of_le i (by
        rw [Scheme.IdealSheafData.stalkIdeal_iSup']
        exact le_iSup_of_le hi le_rfl)
    exact hle.trans
      ((Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp hx)
  let τ : {i : E.ι // i ∈ s} → Fin m := fun i => c ⟨i.1, hix i.1 i.2⟩
  let t : Finset (Fin m) := Finset.univ.image τ
  refine ⟨m, z, ⟨hz, c, hcinj, hc⟩, t, ?_⟩
  apply le_antisymm
  · rw [sncStratumIdeal, Scheme.IdealSheafData.stalkIdeal_iSup']
    apply iSup_le
    intro i
    rw [Scheme.IdealSheafData.stalkIdeal_iSup']
    apply iSup_le
    intro hi
    rw [hc ⟨i, hix i hi⟩]
    apply Ideal.span_le.mpr
    rintro a rfl
    exact Ideal.subset_span ⟨τ ⟨i, hi⟩, by simp [t], rfl⟩
  · apply Ideal.span_le.mpr
    rintro a ⟨j, hj, rfl⟩
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    have hle : (E.component i.1).stalkIdeal x ≤ (sncStratumIdeal E s).stalkIdeal x := by
      rw [sncStratumIdeal, Scheme.IdealSheafData.stalkIdeal_iSup']
      exact le_iSup_of_le i.1 (by
        rw [Scheme.IdealSheafData.stalkIdeal_iSup']
        exact le_iSup_of_le i.2 le_rfl)
    apply hle
    rw [hc ⟨i.1, hix i.1 i.2⟩]
    exact Ideal.subset_span (Set.mem_singleton _)

/-- Every actual closed stratum of an SNC boundary on a smooth scheme is regular. -/
theorem sncStratum_isRegular
    (K : Type u) [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
    [Smooth (T ↘ Spec (CommRingCat.of K))]
    (E : Scheme.DivisorFamily T) (hE : E.IsSnc) (s : Finset E.ι) :
    IsRegular (sncStratumIdeal E s).subscheme :=
  AlgebraicGeometry.HasSncWith.isRegular (T ↘ Spec (CommRingCat.of K))
    (sncStratumIdeal_hasSncWith E hE s)

/-- A single actual nonempty base open makes every closed SNC stratum smooth over the base. -/
theorem proper_snc_strata_exists_common_smooth_base_open
    (K : Type u) [Field K] [CharZero K] {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] (E : Scheme.DivisorFamily T) (hE : E.IsSnc) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ ∀ s : Finset E.ι,
      Smooth (((sncStratumIdeal E s).subschemeι ≫ g) ∣_ V) := by
  apply finite_proper_regular_family_exists_common_smooth_base_open K
    (fun s : Finset E.ι => (sncStratumIdeal E s).subscheme)
    (fun s => (sncStratumIdeal E s).subschemeι ≫ g)
  · intro s
    infer_instance
  · intro s t
    exact (sncStratum_isRegular K E hE s).isRegularAt t

end MixedFujita
