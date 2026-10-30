/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.VeryGeneralClosedPoint
public import MixedFujita.PointClosureSubscheme

/-!
Sets of points of a scheme Y whose closed points are dense over a point w (the form of the
specialization comparison (6) used by section 5).

`ClosedPointsDenseOver K w G` says: for every integral scheme X locally of finite type over K,
every morphism π : X → Y and every point η of X over w, every open set containing η contains a
closed point of the closure of η which maps into G. The comparison (6) is used at such closed
points.

* An open set containing w has this property, over every field: the scheme X is Jacobson.
* The complement of countably many closed sets not containing w has this property when K is
  algebraically closed and uncountable: the closure of η is an integral scheme of finite type over
  K, and a very general closed point of it avoids the countably many proper closed subsets. This
  is the form of (6) in section 2.3 of the manuscript (for a very general point y of the closure
  of w).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

universe u

/-- The closed points over G are dense over w: for every integral scheme X locally of finite type
over K, every morphism π : X → Y and every point η of X over w, every open set containing η
contains a closed point of the closure of η which maps into G. -/
def ClosedPointsDenseOver (K : Type u) [Field K] {Y : Scheme.{u}} (w : Y) (G : Set Y) : Prop :=
  ∀ (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (π : X ⟶ Y) (η : X), π η = w →
    ∀ O : Set X, IsOpen O → η ∈ O →
      ∃ z ∈ O, IsClosed ({z} : Set X) ∧ z ∈ closure ({η} : Set X) ∧ π z ∈ G

variable {K : Type u} [Field K] {Y : Scheme.{u}}

/-- An open set containing w has dense closed points over w. -/
theorem closedPointsDenseOver_of_isOpen {w : Y} {U : Set Y} (hU : IsOpen U) (hw : w ∈ U) :
    ClosedPointsDenseOver K w U := by
  intro X _ _ _ π η hη O hO hηO
  have hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  have hηU : η ∈ π ⁻¹' U := by
    rw [Set.mem_preimage, hη]
    exact hw
  obtain ⟨z, ⟨hzη, hzO, hzU⟩, hzcl⟩ := nonempty_inter_closedPoints
    (Z := closure ({η} : Set X) ∩ (O ∩ π ⁻¹' U)) ⟨η, subset_closure rfl, hηO, hηU⟩
    (isClosed_closure.isLocallyClosed.inter
      (hO.inter (hU.preimage π.continuous)).isLocallyClosed)
  exact ⟨z, hzO, mem_closedPoints_iff.mp hzcl, hzη, hzU⟩

/-- Over an uncountable algebraically closed field, the complement of countably many closed sets
not containing w has dense closed points over w. -/
theorem closedPointsDenseOver_of_countable [IsAlgClosed K] [Uncountable K] {w : Y}
    (Z : ℕ → Set Y) (hZ : ∀ i, IsClosed (Z i)) (hw : ∀ i, w ∉ Z i) :
    ClosedPointsDenseOver K w (⋂ i, (Z i)ᶜ) := by
  intro X _ _ _ π η hη O hO hηO
  have hgen : pointClosureι η (genericPoint (pointClosureScheme η)) = η :=
    pointClosureι_genericPoint η
  obtain ⟨y, hyc, hyO, hyZ⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K)
    (W := pointClosureScheme η) (pointClosureι η ⁻¹' O)
    (hO.preimage (pointClosureι η).continuous)
    ⟨genericPoint (pointClosureScheme η), by rw [Set.mem_preimage, hgen]; exact hηO⟩
    (fun i => pointClosureι η ⁻¹' (π ⁻¹' Z i))
    (fun i => ((hZ i).preimage π.continuous).preimage (pointClosureι η).continuous)
    (fun i h => by
      have hg : genericPoint (pointClosureScheme η) ∈ pointClosureι η ⁻¹' (π ⁻¹' Z i) :=
        h ▸ Set.mem_univ _
      rw [Set.mem_preimage, Set.mem_preimage, hgen, hη] at hg
      exact hw i hg)
  refine ⟨pointClosureι η y, hyO, ?_, ?_, ?_⟩
  · have h1 := (pointClosureι η).isClosedEmbedding.isClosedMap _ hyc
    rwa [Set.image_singleton] at h1
  · rw [← range_pointClosureι η]
    exact Set.mem_range_self y
  · rw [Set.mem_iInter]
    exact fun i hi => hyZ i hi

end MixedFujita
