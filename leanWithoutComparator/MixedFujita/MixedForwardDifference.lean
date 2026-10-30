/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Tactic.Abel

/-! Mathlib差分作用素による混合差分の対称性と加法欠損。 See reports/check-219-mixed-euler-intersection-foundation.json for the verified scope. The ordinary mixed-intersection dimension bound in dimension at least two remains unproved. -/

@[expose] public section
namespace MixedFujita

/-- Successive forward differences in specified, possibly distinct directions. -/
def mixedForwardDifference {A : Type*} [AddCommMonoid A]
    (D : List A) (f : A → ℤ) : A → ℤ := D.foldr fwdDiff f


/-- The defining cut recurrence in a specified first direction. -/
theorem mixedForwardDifference_cons {A : Type*} [AddCommMonoid A]
    (D : List A) (H : A) (f : A → ℤ) (E : A) :
    mixedForwardDifference (H :: D) f E =
      mixedForwardDifference D f (E + H) - mixedForwardDifference D f E := rfl


/-- Mixed differences are invariant under every permutation of directions. -/
theorem mixedForwardDifference_perm {A : Type*} [AddCommMonoid A]
    {D F : List A} (h : D.Perm F) (f : A → ℤ) :
    mixedForwardDifference D f = mixedForwardDifference F f := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [mixedForwardDifference, List.foldr_cons] at *; rw [ih]
  | swap a b D =>
    funext E
    simp only [mixedForwardDifference_cons]
    rw [add_right_comm E a b]
    abel
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂


/-- The exact nonadditivity defect is the next mixed difference. -/
theorem mixedForwardDifference_add_direction {A : Type*} [AddCommMonoid A]
    (D : List A) (H J : A) (f : A → ℤ) (E : A) :
    mixedForwardDifference ((H + J) :: D) f E =
      mixedForwardDifference (H :: D) f E + mixedForwardDifference (J :: D) f E +
        mixedForwardDifference (H :: J :: D) f E := by
  simp only [mixedForwardDifference_cons, add_assoc]
  abel

end MixedFujita
