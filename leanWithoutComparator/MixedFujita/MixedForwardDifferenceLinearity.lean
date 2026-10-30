/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MixedForwardDifference

/-! 混合差分の係数加法性と非空定数差分消滅。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
namespace MixedFujita

/-- Mixed forward differences preserve addition of the actual Euler functions. -/
theorem mixedForwardDifference_add_functions {A : Type*} [AddCommMonoid A]
    (D : List A) (f g : A → ℤ) :
    mixedForwardDifference D (f + g) = mixedForwardDifference D f + mixedForwardDifference D g := by
  induction D with
  | nil => rfl
  | cons H D ih =>
    change fwdDiff H (mixedForwardDifference D (f + g)) = _
    rw [ih, fwdDiff_add]
    rfl


/-- Every mixed difference of the zero Euler function vanishes. -/
theorem mixedForwardDifference_zero_function {A : Type*} [AddCommMonoid A]
    (D : List A) : mixedForwardDifference D (fun _ => (0 : ℤ)) = fun _ => 0 := by
  induction D with
  | nil => rfl
  | cons H D ih =>
    change fwdDiff H (mixedForwardDifference D (fun _ => (0 : ℤ))) = _
    rw [ih, fwdDiff_const]


/-- Every nonempty mixed difference of a constant function vanishes. -/
theorem mixedForwardDifference_nonempty_const {A : Type*} [AddCommMonoid A]
    (D : List A) (H : A) (c : ℤ) :
    mixedForwardDifference (H :: D) (fun _ => c) = fun _ => 0 := by
  induction D generalizing H with
  | nil => exact fwdDiff_const H c
  | cons J D ih =>
    change fwdDiff H (mixedForwardDifference (J :: D) (fun _ => c)) = _
    rw [ih J, fwdDiff_const]

end MixedFujita
