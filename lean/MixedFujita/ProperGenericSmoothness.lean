/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularEssentiallyFiniteTypeSmooth
public import MixedFujita.HironakaSNCModelExistence
public import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-!
At every regular point above the generic point of an integral characteristic-zero
base, the actual stalk map is formally smooth. For a proper morphism with regular
source, remove the actual closed image of the nonsmooth locus. Its complement is
a nonempty base open over which the original morphism is smooth. No dominant,
flatness, smooth-fibre or good-open certificate is supplied.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A regular point over the generic point of an integral characteristic-zero base is smooth. -/
theorem regular_point_smooth_over_generic_base
    (K : Type u) [Field K] [CharZero K] {T Y : Scheme.{u}}
    [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [LocallyOfFinitePresentation g]
    (t : T) (ht : g t = genericPoint Y) (hreg : T.IsRegularAt t) :
    t ∈ g.smoothLocus := by
  have hfield : IsField (Y.presheaf.stalk (g t)) := by
    rw [ht]
    exact Field.toIsField Y.functionField
  letI := hfield.toField
  letI := (Y ↘ Spec (CommRingCat.of K)).stalkAlgebra (g t)
  letI : CharZero (Y.presheaf.stalk (g t)) :=
    charZero_of_injective_algebraMap (algebraMap K (Y.presheaf.stalk (g t))).injective
  rw [Scheme.Hom.mem_smoothLocus]
  have hft := LocallyOfFiniteType.stalkMap g t
  algebraize [(g.stalkMap t).hom]
  letI : IsRegularLocalRing (T.presheaf.stalk t) := hreg
  exact formallySmooth_of_regular_essFiniteType_perfectField
    (Y.presheaf.stalk (g t)) (T.presheaf.stalk t)

/-- Remove the closed proper image of the actual nonsmooth locus of a proper regular source. -/
theorem proper_regular_exists_nonempty_base_open_smooth
    (K : Type u) [Field K] [CharZero K] {T Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] (hreg : ∀ t : T, T.IsRegularAt t) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧
      ∀ t : T, g t ∈ V → t ∈ g.smoothLocus := by
  let Z : Set T := (g.smoothLocus : Set T)ᶜ
  have hZ : IsClosed Z := g.smoothLocus.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(g '' Z)ᶜ, (g.isClosedMap Z hZ).isOpen_compl⟩
  have hη : genericPoint Y ∈ V := by
    rintro ⟨t, ht, heq⟩
    exact ht (regular_point_smooth_over_generic_base K g t heq (hreg t))
  refine ⟨V, hη, ?_⟩
  intro t ht
  by_contra hbad
  exact ht ⟨t, hbad, rfl⟩

/-- Smooth sources over a characteristic-zero field supply the regularity internally. -/
theorem proper_smooth_source_exists_nonempty_base_open_smooth
    (K : Type u) [Field K] [CharZero K] {T Y : Scheme.{u}}
    [T.Over (Spec (CommRingCat.of K))] [Smooth (T ↘ Spec (CommRingCat.of K))]
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    (g : T ⟶ Y) [IsProper g] :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧
      ∀ t : T, g t ∈ V → t ∈ g.smoothLocus := by
  apply proper_regular_exists_nonempty_base_open_smooth K g
  intro t
  apply Scheme.isRegularAt_of_mem_smoothLocus (T ↘ Spec (CommRingCat.of K))
  rw [Scheme.Hom.smoothLocus_eq_top]
  trivial

end MixedFujita
