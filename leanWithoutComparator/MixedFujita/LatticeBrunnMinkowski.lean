/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import LeanPool.Isoperimetric.BrunnMinkowski
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
The finite lattice inequality used in Section 4, between (tangent) and
(slice-growth). We thicken the input lattice sets by *open* unit cubes.
This makes their Minkowski sum open. Closed cubes on the right cover the
sum, so no measurability theorem about arbitrary Minkowski sums is needed.
-/

@[expose] public section

namespace MixedFujita

open MeasureTheory Set
open scoped Pointwise

def openUnitCube {d : ℕ} (p : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioo (p i : ℝ) ((p i : ℝ) + 1))

def closedUnitCube {d : ℕ} (p : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.Icc (fun i => (p i : ℝ)) (fun i => (p i : ℝ) + 1)

def openThickening {d : ℕ} (E : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  ⋃ p ∈ E, openUnitCube p

def closedThickening {d : ℕ} (E : Finset (Fin d → ℤ)) : Set (Fin d → ℝ) :=
  ⋃ p ∈ E, closedUnitCube p

def binaryVectors (d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => {0, 1})

def thickenedSum {d : ℕ} (E F : Finset (Fin d → ℤ)) : Finset (Fin d → ℤ) :=
  E + F + binaryVectors d

theorem openUnitCube_isOpen {d : ℕ} (p : Fin d → ℤ) : IsOpen (openUnitCube p) :=
  isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

theorem openUnitCube_volume {d : ℕ} (p : Fin d → ℤ) : volume (openUnitCube p) = 1 := by
  simp [openUnitCube, Real.volume_pi_Ioo]

theorem closedUnitCube_volume {d : ℕ} (p : Fin d → ℤ) : volume (closedUnitCube p) = 1 := by
  simp [closedUnitCube, Real.volume_Icc_pi]

theorem openUnitCube_disjoint {d : ℕ} {p q : Fin d → ℤ} (hpq : p ≠ q) :
    Disjoint (openUnitCube p) (openUnitCube q) := by
  apply Set.disjoint_left.mpr
  intro x hp hq
  apply hpq
  funext i
  have hp' := Set.mem_pi.mp hp i (Set.mem_univ i)
  have hq' := Set.mem_pi.mp hq i (Set.mem_univ i)
  have hfp : ⌊x i⌋ = p i := Int.floor_eq_iff.mpr ⟨hp'.1.le, hp'.2⟩
  have hfq : ⌊x i⌋ = q i := Int.floor_eq_iff.mpr ⟨hq'.1.le, hq'.2⟩
  exact hfp.symm.trans hfq

theorem openThickening_isOpen {d : ℕ} (E : Finset (Fin d → ℤ)) :
    IsOpen (openThickening E) :=
  isOpen_iUnion fun p => isOpen_iUnion fun _ => openUnitCube_isOpen p

theorem openThickening_volume {d : ℕ} (E : Finset (Fin d → ℤ)) :
    volume (openThickening E) = E.card := by
  rw [openThickening, measure_biUnion_finset
    (fun _ _ _ _ hpq => openUnitCube_disjoint hpq)
    (fun p _ => (openUnitCube_isOpen p).measurableSet)]
  simp [openUnitCube_volume]

theorem closedThickening_volume_le {d : ℕ} (E : Finset (Fin d → ℤ)) :
    volume (closedThickening E) ≤ E.card := by
  calc
    volume (closedThickening E) ≤ ∑ p ∈ E, volume (closedUnitCube p) :=
      measure_biUnion_finset_le E closedUnitCube
    _ = E.card := by simp [closedUnitCube_volume]

theorem openThickening_nonempty {d : ℕ} {E : Finset (Fin d → ℤ)} (hE : E.Nonempty) :
    (openThickening E).Nonempty := by
  obtain ⟨p, hp⟩ := hE
  refine ⟨fun i => (p i : ℝ) + 1 / 2, ?_⟩
  refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, ?_⟩⟩
  intro i _
  constructor <;> dsimp <;> linarith

/-- Coordinatewise rounding chooses the binary correction explicitly. -/
theorem thickening_add_subset {d : ℕ} (E F : Finset (Fin d → ℤ)) :
    openThickening E + openThickening F ⊆ closedThickening (thickenedSum E F) := by
  classical
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨p, hp, hx⟩ := Set.mem_iUnion.mp hx |>.imp fun _ => Set.mem_iUnion.mp
  obtain ⟨q, hq, hy⟩ := Set.mem_iUnion.mp hy |>.imp fun _ => Set.mem_iUnion.mp
  let r : Fin d → ℤ := fun i => if x i + y i < (p i : ℝ) + (q i : ℝ) + 1 then 0 else 1
  have hr : r ∈ binaryVectors d := by
    apply Fintype.mem_piFinset.mpr
    intro i
    dsimp [r]
    split <;> simp
  have hmem : p + q + r ∈ thickenedSum E F :=
    Finset.mem_add.mpr ⟨p + q, Finset.mem_add.mpr ⟨p, hp, q, hq, rfl⟩, r, hr, rfl⟩
  refine Set.mem_iUnion.mpr ⟨p + q + r, Set.mem_iUnion.mpr ⟨hmem, ?_⟩⟩
  constructor
  · intro i
    have hx' := Set.mem_pi.mp hx i (Set.mem_univ i)
    have hy' := Set.mem_pi.mp hy i (Set.mem_univ i)
    change ((p i + q i + r i : ℤ) : ℝ) ≤ x i + y i
    simp only [Int.cast_add]
    dsimp [r]
    split <;> simp only [Int.cast_zero, Int.cast_one] <;> linarith [hx'.1, hy'.1]
  · intro i
    have hx' := Set.mem_pi.mp hx i (Set.mem_univ i)
    have hy' := Set.mem_pi.mp hy i (Set.mem_univ i)
    change x i + y i ≤ ((p i + q i + r i : ℤ) : ℝ) + 1
    simp only [Int.cast_add]
    dsimp [r]
    split <;> simp only [Int.cast_zero, Int.cast_one] <;> linarith [hx'.2, hy'.2]

/-- The discrete BM inequality with the `{0,1}^d` correction, in ENNReal. -/
theorem lattice_brunn_minkowski_ennreal {d : ℕ}
    (E F : Finset (Fin (d + 1) → ℤ)) (hE : E.Nonempty) (hF : F.Nonempty) :
    (E.card : ENNReal) ^ ((d : ℝ) + 1)⁻¹ + (F.card : ENNReal) ^ ((d : ℝ) + 1)⁻¹ ≤
      ((thickenedSum E F).card : ENNReal) ^ ((d : ℝ) + 1)⁻¹ := by
  have h := brunn_minkowski (openThickening_nonempty hE)
    (openThickening_isOpen E).measurableSet (openThickening_nonempty hF)
    (openThickening_isOpen F).measurableSet (openThickening_isOpen E).add_right.measurableSet
  rw [openThickening_volume, openThickening_volume] at h
  refine h.trans ?_
  apply ENNReal.rpow_le_rpow
  · exact (measure_mono (thickening_add_subset E F)).trans (closedThickening_volume_le _)
  · positivity

/-- The real-valued version used by the slice-growth argument. -/
theorem lattice_brunn_minkowski {d : ℕ}
    (E F : Finset (Fin (d + 1) → ℤ)) (hE : E.Nonempty) (hF : F.Nonempty) :
    (E.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ + (F.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ ≤
      ((thickenedSum E F).card : ℝ) ^ ((d : ℝ) + 1)⁻¹ := by
  have hn (k : ℕ) : (k : ENNReal) ^ ((d : ℝ) + 1)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)
  have h := ENNReal.toReal_mono (hn _) (lattice_brunn_minkowski_ennreal E F hE hF)
  simpa only [ENNReal.toReal_add (hn _) (hn _), ← ENNReal.toReal_rpow,
    ENNReal.toReal_natCast] using h

/-- The form needed when the graded semigroup supplies an inclusion. -/
theorem lattice_brunn_minkowski_of_subset {d : ℕ}
    (E F G : Finset (Fin (d + 1) → ℤ)) (hE : E.Nonempty) (hF : F.Nonempty)
    (hsubset : thickenedSum E F ⊆ G) :
    (E.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ + (F.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ ≤
      (G.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ := by
  have hc : ((thickenedSum E F).card : ℝ) ≤ G.card := by
    exact_mod_cast Finset.card_le_card hsubset
  exact (lattice_brunn_minkowski E F hE hF).trans
    (Real.rpow_le_rpow (by positivity) hc (by positivity))

end MixedFujita
