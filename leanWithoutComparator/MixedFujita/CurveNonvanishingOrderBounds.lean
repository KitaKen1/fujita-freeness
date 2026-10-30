/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionNonvanishingOpen
public import MixedFujita.ActualCurveRestrictionOrderBounds

/-!
The source order is bounded by the actual curve degree when the actual
curve image meets the constructed source section nonvanishing open.
The actual pulled section's nonzeroness, its coefficient compatibility,
and the order inequality are all derived. Selecting such a curve through
a specified point and bounding its degree uniformly remain to be proved.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable {K : Type u} [Field K] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem cartierSourceOrder_le_degree_of_curve_image_meets_nonvanishingOpen
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (y : Y) (hClosed : IsClosed {y}) (s : Γ(D.sheaf, ⊤))
    (hHit : ∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen D s) :
    cartierSectionVanishingOrder D (φ y) s ≤ (properCurveCartierDegree (K := K) hY E).toNat := by
  exact cartierSourceOrder_le_degree_of_actual_curve_pullback (K := K) hY D φ E a y hClosed s
    ((cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen D φ s).mpr hHit)

theorem cartierSourceOrder_le_linearBound_of_graded_curve_image_meets_nonvanishingOpen
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (A : CartierDivisor Y) (j : ℕ)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ (j • A).sheaf)
    (y : Y) (hClosed : IsClosed {y}) (s : Γ(D.sheaf, ⊤))
    (hHit : ∃ z : Y, φ z ∈ cartierSectionNonvanishingOpen D s) :
    cartierSectionVanishingOrder D (φ y) s ≤ j * properCurveOrderBound (K := K) hY A := by
  exact cartierSourceOrder_le_linearBound_of_actual_graded_curve_pullback
    (K := K) hY D φ A j a y hClosed s
      ((cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen D φ s).mpr hHit)

end MixedFujita
