/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricSmoothTaylor
public import MixedFujita.CartierGradedTaylor

/-!
At an algebraically closed closed point of an actual smooth integral scheme
of geometric dimension n, one constructed coordinate system and one chosen
Cartier local equation give all graded Taylor maps simultaneously. They are
injective, preserve intrinsic order, and multiply. When actual global section
spaces are finite dimensional, their full initial-exponent family has the
correct dimension counts and semigroup law. Projectivity must still supply
that finite dimensionality and geometric growth; it is not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem geometricSmoothCartier_closedPoint_exists_gradedTaylor (n : ℕ)
    (hn : topologicalKrullDim X = n) (A : CartierDivisor X) (x : X) (hClosed : IsClosed {x}) :
    ∃ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ j, Function.Injective (cartierGradedTaylor A x f hf e j)) ∧
        (∀ j s, (cartierGradedTaylor A x f hf e j s).order =
          cartierSectionVanishingOrder (j • A) x s) ∧
        ∀ j h s t,
          cartierGradedTaylor A x f hf e (j + h) (cartierGradedSectionProduct A j h s t) =
            cartierGradedTaylor A x f hf e j s * cartierGradedTaylor A x f hf e h t := by
  let : IsNoetherianRing (X.presheaf.stalk x) := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨e, _⟩ := geometricSmoothScheme_closedPoint_exists_stalkCoordinates (K := K) n hn x hClosed
  obtain ⟨f, hf⟩ := A.exists_isLocalEquationAt x
  refine ⟨f, hf, e, fun j => cartierGradedTaylor_injective A x f hf e j, ?_, ?_⟩
  · intro j s
    rw [cartierGradedTaylor_fin_eq]
    exact cartierTaylorCoordinates_order_eq_vanishingOrder (j • A) x (f ^ j)
      (cartierLocalEquation_pow A x f hf j) e s
  · exact fun j h s t => cartierGradedTaylor_product A x f hf e j h s t

theorem geometricSmoothCartier_closedPoint_exists_gradedExponentFamily (n : ℕ)
    (hn : topologicalKrullDim X = n) (A : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)] (m : MonomialOrder (Fin n)) :
    ∃ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ j, (cartierGradedInitialExponents A x f hf m e j).card =
          Module.finrank K Γ((j • A).sheaf, ⊤)) ∧
        ∀ j h,
          cartierGradedInitialExponents A x f hf m e j +
            cartierGradedInitialExponents A x f hf m e h ⊆
              cartierGradedInitialExponents A x f hf m e (j + h) := by
  let : IsNoetherianRing (X.presheaf.stalk x) := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨f, hf, e, _⟩ :=
    geometricSmoothCartier_closedPoint_exists_gradedTaylor (K := K) n hn A x hClosed
  exact ⟨f, hf, e, fun j => cartierGradedInitialExponents_card A x f hf m e j,
    fun j h => cartierGradedInitialExponents_add_subset A x f hf m e j h⟩

end MixedFujita
