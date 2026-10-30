/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperGenericSmoothness

/-!
Convert the actual smooth-locus avoidance open to smoothness of the actual
base-restricted morphism. A finite collection of proper regular sources has a
single nonempty base open on which all their restricted morphisms are smooth.
This includes disconnected and vertical sources, as required for SNC strata.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Smoothness over an actual base open follows from its full inverse image lying in the smooth locus. -/
theorem smooth_morphismRestrict_of_preimage_mem_smoothLocus
    {T Y : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFinitePresentation g]
    (V : Y.Opens) (hV : ∀ t : T, g t ∈ V → t ∈ g.smoothLocus) : Smooth (g ∣_ V) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro t _
  rw [Scheme.Hom.mem_smoothLocus]
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap g V t)).mpr
      ((Scheme.Hom.mem_smoothLocus).mp (hV t.1 t.2))

/-- A proper regular source gives an actual smooth restricted morphism on a nonempty base open. -/
theorem proper_regular_exists_smooth_morphismRestrict
    (K : Type u) [Field K] [CharZero K] {T Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] (hreg : ∀ t : T, T.IsRegularAt t) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ Smooth (g ∣_ V) := by
  obtain ⟨V, hηV, hV⟩ := proper_regular_exists_nonempty_base_open_smooth K g hreg
  exact ⟨V, hηV, smooth_morphismRestrict_of_preimage_mem_smoothLocus g V hV⟩

/-- All members of a finite proper regular family become smooth over the same actual base open. -/
theorem finite_proper_regular_family_exists_common_smooth_base_open
    (K : Type u) [Field K] [CharZero K] {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    {ι : Type u} [Finite ι] (T : ι → Scheme.{u}) (g : ∀ i, T i ⟶ Y)
    (hproper : ∀ i, IsProper (g i)) (hreg : ∀ i (t : T i), (T i).IsRegularAt t) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ ∀ i, Smooth (g i ∣_ V) := by
  classical
  letI : ∀ i, IsProper (g i) := hproper
  have hex (i : ι) : ∃ U : Y.Opens, genericPoint Y ∈ U ∧
      ∀ t : T i, g i t ∈ U → t ∈ (g i).smoothLocus := by
    letI := hproper i
    exact proper_regular_exists_nonempty_base_open_smooth K (g i) (hreg i)
  choose U hη hU using hex
  let V : Y.Opens := ⟨⋂ i, (U i : Set Y), isOpen_iInter_of_finite (fun i => (U i).isOpen)⟩
  refine ⟨V, Set.mem_iInter.mpr hη, ?_⟩
  intro i
  letI := hproper i
  apply smooth_morphismRestrict_of_preimage_mem_smoothLocus (g i) V
  intro t ht
  exact hU i t (Set.mem_iInter.mp ht i)

end MixedFujita
