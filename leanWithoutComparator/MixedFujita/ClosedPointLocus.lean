/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
A locus defined using K-valued data should be compared with a scheme closed set only at closed
points. Its membership at nonclosed scheme points need not agree with that closed set. In a
Jacobson space the closed representative, if it exists, is unique and is the closure of its
closed points. This distinction matters for bases chosen over K in profile realization.
-/

@[expose] public section

open TopologicalSpace Topology

namespace MixedFujita

/-- A set has a closed representative with the same closed points. No claim is made about its
membership at nonclosed points. -/
def IsClosedOnClosedPoints {T : Type*} [TopologicalSpace T] (s : Set T) : Prop :=
  ∃ Z : Set T, IsClosed Z ∧ ∀ x : T, IsClosed ({x} : Set T) → (x ∈ s ↔ x ∈ Z)

/-- Actual closedness implies closedness on closed points. -/
theorem isClosedOnClosedPoints_of_isClosed {T : Type*} [TopologicalSpace T] {s : Set T}
    (hs : IsClosed s) : IsClosedOnClosedPoints s := ⟨s, hs, fun _ _ => Iff.rfl⟩

/-- On a Jacobson space a closed representative is the closure of the realized closed points. -/
theorem closedPointLocus_representative_eq_closure {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {s Z : Set T} (hZ : IsClosed Z)
    (hrep : ∀ x : T, IsClosed ({x} : Set T) → (x ∈ s ↔ x ∈ Z)) :
    Z = closure (s ∩ closedPoints T) := by
  have h : s ∩ closedPoints T = Z ∩ closedPoints T := by
    ext x
    exact and_congr_left fun hx => hrep x (mem_closedPoints_iff.mp hx)
  rw [h, closure_inter_closedPoints hZ]

/-- A canonical criterion for closedness on closed points, requiring no chosen representative. -/
theorem isClosedOnClosedPoints_iff_closure {T : Type*} [TopologicalSpace T] [JacobsonSpace T]
    (s : Set T) : IsClosedOnClosedPoints s ↔
      ∀ x : T, IsClosed ({x} : Set T) → (x ∈ s ↔ x ∈ closure (s ∩ closedPoints T)) := by
  constructor
  · rintro ⟨Z, hZ, hrep⟩ x hx
    rw [← closedPointLocus_representative_eq_closure hZ hrep]
    exact hrep x hx
  · intro h
    exact ⟨closure (s ∩ closedPoints T), isClosed_closure, h⟩

/-- The standard obstruction to full-scheme closedness: a locus can contain all closed points
and still omit a scheme point. Closedness on closed points does not have this obstruction. -/
theorem not_isClosed_of_contains_closedPoints {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {s : Set T} (hs : closedPoints T ⊆ s) {η : T} (hη : η ∉ s) :
    ¬ IsClosed s := by
  intro hcl
  have h : (Set.univ : Set T) ⊆ s := by
    rw [← closure_closedPoints]
    exact closure_minimal hs hcl
  exact hη (h trivial)

end MixedFujita
