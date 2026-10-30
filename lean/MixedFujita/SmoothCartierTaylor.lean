/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothSchemeCoordinates
public import MixedFujita.CartierVanishingOrder

/-!
The actual global sections of a Cartier divisor on a smooth integral scheme
have an injective K-linear Taylor map at a K-rational local point. Its
power-series order is the actual, frame-independent vanishing order.
Completed coordinates and stalk Noetherianity are derived from smoothness.
Finite dimensionality of the global section space and identification of
the variable count with geometric dimension are not claimed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem smoothCartier_exists_injectiveTaylor (D : CartierDivisor X) (x : X)
    (β : X.presheaf.stalk x →ₐ[K] K)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
      ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
        cartierSectionVanishingOrder D x s := by
  let : IsNoetherianRing (X.presheaf.stalk x) := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨n, e, _⟩ := smoothScheme_rationalPoint_exists_stalkCoordinates x β
  exact ⟨n, e, cartierTaylorCoordinates_injective D x f hf e,
    cartierTaylorCoordinates_order_eq_vanishingOrder D x f hf e⟩

end MixedFujita
