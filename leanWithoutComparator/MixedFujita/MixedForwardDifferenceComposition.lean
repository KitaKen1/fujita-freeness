/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MixedForwardDifferenceLinearity

/-! 実混合差分の連結合成と方向の並べ替え。 See reports/check-223-multivariate-euler-intersection.json for the verified scope. Mixed positivity and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
namespace MixedFujita
open Finset
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Concatenation composes the actual mixed forward differences. -/
theorem mixedForwardDifference_append {A : Type*} [AddCommMonoid A]
    (D F : List A) (f : A → ℤ) :
    mixedForwardDifference (D ++ F) f = mixedForwardDifference D (mixedForwardDifference F f) := by
  simp only [mixedForwardDifference, List.foldr_append]


/-- The last first-order difference can be moved to the front. -/
theorem mixedForwardDifference_right_singleton {A : Type*} [AddCommMonoid A]
    (D : List A) (H : A) (f : A → ℤ) :
    mixedForwardDifference D (fwdDiff H f) = mixedForwardDifference (H :: D) f := by
  change mixedForwardDifference D (mixedForwardDifference [H] f) = _
  rw [← mixedForwardDifference_append D [H] f]
  exact mixedForwardDifference_perm List.perm_append_comm f

end MixedFujita
