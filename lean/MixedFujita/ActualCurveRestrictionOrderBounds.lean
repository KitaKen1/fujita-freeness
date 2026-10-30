/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierActualPullbackOrder

/-!
Transfer the actual proper smooth integral curve degree bound to the
source intrinsic Cartier order using the actual pulled global section.
No coefficient equality, transition unit, or order inequality is an
input. Nonzero actual pullback and its actual target Cartier presentation
are required. Choosing a Bertini curve with nonzero restriction and
identifying a uniform ambient intersection degree remain separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable {K : Type u} [Field K] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem cartierSourceOrder_le_degree_of_actual_curve_pullback
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (y : Y) (hClosed : IsClosed {y}) (s : Γ(D.sheaf, ⊤))
    (hs : modulePullbackGlobalSections φ D.sheaf s ≠ 0) :
    cartierSectionVanishingOrder D (φ y) s ≤ (properCurveCartierDegree (K := K) hY E).toNat := by
  exact (cartierSourceOrder_le_actualGlobalPullback D φ E a y s).trans
    (properSmoothCurve_closedPoint_vanishingOrder_le_degree (K := K) hY E y hClosed _
      ((cartierPullbackGlobalSectionViaIso_ne_zero_iff D φ E a s).mpr hs))

theorem cartierSourceOrder_le_linearBound_of_actual_graded_curve_pullback
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (A : CartierDivisor Y) (j : ℕ)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ (j • A).sheaf)
    (y : Y) (hClosed : IsClosed {y}) (s : Γ(D.sheaf, ⊤))
    (hs : modulePullbackGlobalSections φ D.sheaf s ≠ 0) :
    cartierSectionVanishingOrder D (φ y) s ≤ j * properCurveOrderBound (K := K) hY A := by
  exact (cartierSourceOrder_le_actualGlobalPullback D φ (j • A) a y s).trans
    (properSmoothCurve_closedPoint_gradedVanishingOrder_le_linearBound
      (K := K) hY A j y hClosed _
        ((cartierPullbackGlobalSectionViaIso_ne_zero_iff D φ (j • A) a s).mpr hs))

end MixedFujita
