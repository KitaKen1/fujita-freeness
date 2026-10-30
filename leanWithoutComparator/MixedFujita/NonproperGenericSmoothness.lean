/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProperGenericSmoothness
public import MixedFujita.GenericSmoothBaseOpen
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
Generic smoothness without properness (step 9). A constructible set either contains an open
neighbourhood of a generic point or misses one (`isConstructible_nhds_genericPoint`: the property
is preserved by the Boolean operations, and an open set containing a point specializing from the
generic point contains the generic point). The non-smooth locus of a morphism from a regular
noetherian scheme of finite presentation to a qcqs integral scheme over a field of characteristic
zero is closed, hence constructible, its image is constructible by Chevalley's theorem and misses
the generic point (regular points over the generic point are smooth), so a whole open
neighbourhood of the generic point has smooth fibres
(`exists_open_genericPoint_smooth_of_regular`). This is the generic smoothness of a log
resolution of a family over the base, without compactifying the family.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Constructible

variable {X : Type*} [TopologicalSpace X]

/-- A constructible set either contains an open neighbourhood of a generic point or is disjoint
from one. -/
theorem isConstructible_nhds_genericPoint {η : X} (hη : ∀ x, η ⤳ x) {C : Set X}
    (hC : IsConstructible C) :
    (η ∈ C → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ C) ∧
      (η ∉ C → ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ⊆ Cᶜ) := by
  induction hC using BooleanSubalgebra.closure_bot_sup_induction with
  | mem s hs =>
    refine ⟨fun h => ⟨s, hs.1, h, le_rfl⟩, fun h => ⟨Set.univ, isOpen_univ, trivial, ?_⟩⟩
    intro x _ hx
    exact h ((hη x).mem_open hs.1 hx)
  | bot =>
    exact ⟨fun h => absurd h (Set.notMem_empty _),
      fun _ => ⟨Set.univ, isOpen_univ, trivial, fun x _ => Set.notMem_empty x⟩⟩
  | sup s _ t _ hs ht =>
    constructor
    · intro h
      rcases h with h | h
      · obtain ⟨U, hU, hηU, hUs⟩ := hs.1 h
        exact ⟨U, hU, hηU, hUs.trans Set.subset_union_left⟩
      · obtain ⟨U, hU, hηU, hUt⟩ := ht.1 h
        exact ⟨U, hU, hηU, hUt.trans Set.subset_union_right⟩
    · intro h
      obtain ⟨U, hU, hηU, hUs⟩ := hs.2 fun h' => h (Or.inl h')
      obtain ⟨U', hU', hηU', hUt⟩ := ht.2 fun h' => h (Or.inr h')
      refine ⟨U ∩ U', hU.inter hU', ⟨hηU, hηU'⟩, fun x hx hxst => ?_⟩
      rcases hxst with hx' | hx'
      · exact hUs hx.1 hx'
      · exact hUt hx.2 hx'
  | compl s _ hs =>
    constructor
    · intro h
      exact hs.2 h
    · intro h
      obtain ⟨U, hU, hηU, hUs⟩ := hs.1 (not_not.mp h)
      exact ⟨U, hU, hηU, by rw [compl_compl]; exact hUs⟩

end Constructible

section GenericSmooth

/-- Generic smoothness without properness: a morphism of finite presentation from a regular
noetherian scheme to a qcqs integral scheme over a field of characteristic zero is smooth over an
open neighbourhood of the generic point. -/
theorem exists_open_genericPoint_smooth_of_regular (K : Type u) [Field K] [CharZero K]
    {T Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsNoetherian T] (g : T ⟶ Y) [LocallyOfFinitePresentation g]
    [QuasiCompact g] (hreg : ∀ t : T, T.IsRegularAt t) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ ∀ t : T, g t ∈ V → t ∈ g.smoothLocus := by
  let Z : Set T := (g.smoothLocus : Set T)ᶜ
  have hZ : IsConstructible Z :=
    (IsCompact.isConstructible (NoetherianSpace.isCompact _) g.smoothLocus.isOpen).compl
  have hgZ : IsConstructible (g '' Z) := g.isConstructible_image hZ
  have hη : genericPoint Y ∉ g '' Z := by
    rintro ⟨t, ht, heq⟩
    exact ht (regular_point_smooth_over_generic_base K g t heq (hreg t))
  obtain ⟨U, hU, hηU, hUZ⟩ := (isConstructible_nhds_genericPoint
    (fun x => (genericPoint_spec Y).specializes (Set.mem_univ x)) hgZ).2 hη
  refine ⟨⟨U, hU⟩, hηU, fun t ht => ?_⟩
  by_contra hbad
  exact hUZ ht ⟨t, hbad, rfl⟩

/-- In particular the restriction over that open is smooth. -/
theorem exists_open_genericPoint_smooth_morphismRestrict_of_regular (K : Type u) [Field K]
    [CharZero K] {T Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsNoetherian T] (g : T ⟶ Y)
    [LocallyOfFinitePresentation g] [QuasiCompact g] (hreg : ∀ t : T, T.IsRegularAt t) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ Smooth (g ∣_ V) := by
  obtain ⟨V, hηV, hV⟩ := exists_open_genericPoint_smooth_of_regular K g hreg
  exact ⟨V, hηV, smooth_morphismRestrict_of_preimage_mem_smoothLocus g V hV⟩

end GenericSmooth

end MixedFujita
