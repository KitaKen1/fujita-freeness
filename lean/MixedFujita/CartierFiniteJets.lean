/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricGradedTaylor
public import MixedFujita.TaylorFiniteJets

/-!
An actual intrinsic order bound at a closed point of a smooth integral
scheme of geometric dimension n gives finite-dimensional Cartier global
sections and an explicit (d+1)^n dimension bound. This uses constructed
coordinates and finite jets, without assuming section finite dimensionality.
Per-degree bounds also supply the graded initial-exponent family. Deriving
these order bounds from projectivity and divisor intersections remains open.
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

theorem geometricSmoothCartier_closedPoint_exists_injectiveFiniteJet (n : ℕ)
    (hn : topologicalKrullDim X = n) (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (d : ℕ) (hb : ∀ s : Γ(D.sheaf, ⊤), s ≠ 0 → cartierSectionVanishingOrder D x s ≤ d) :
    ∃ J : Γ(D.sheaf, ⊤) →ₗ[K] ((Fin n → Fin (d + 1)) → K), Function.Injective J := by
  obtain ⟨f, hf, e, _, ho⟩ :=
    geometricSmoothCartier_closedPoint_exists_TaylorData (K := K) n hn D x hClosed
  let F := cartierTaylorCoordinates D x f hf e
  have hF : ∀ s, s ≠ 0 → (F s).order ≤ d := fun s hs => (ho s).trans_le (hb s hs)
  exact ⟨(powerSeriesBoxJet n d).comp F, linearTaylorBoxJet_injective n d F hF⟩

theorem geometricSmoothCartier_closedPoint_finiteDimensional_of_order_bound (n : ℕ)
    (hn : topologicalKrullDim X = n) (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (d : ℕ) (hb : ∀ s : Γ(D.sheaf, ⊤), s ≠ 0 → cartierSectionVanishingOrder D x s ≤ d) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  obtain ⟨J, hJ⟩ :=
    geometricSmoothCartier_closedPoint_exists_injectiveFiniteJet (K := K) n hn D x hClosed d hb
  exact FiniteDimensional.of_injective J hJ

theorem geometricSmoothCartier_closedPoint_finrank_le_of_order_bound (n : ℕ)
    (hn : topologicalKrullDim X = n) (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (d : ℕ) (hb : ∀ s : Γ(D.sheaf, ⊤), s ≠ 0 → cartierSectionVanishingOrder D x s ≤ d) :
    Module.finrank K Γ(D.sheaf, ⊤) ≤ (d + 1) ^ n := by
  obtain ⟨J, hJ⟩ :=
    geometricSmoothCartier_closedPoint_exists_injectiveFiniteJet (K := K) n hn D x hClosed d hb
  have H := LinearMap.finrank_le_finrank_of_injective hJ
  simpa only [Module.finrank_pi, Fintype.card_fun, Fintype.card_fin] using H

theorem geometricSmoothCartier_closedPoint_gradedExponents_of_order_bounds (n : ℕ)
    (hn : topologicalKrullDim X = n) (A : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (d : ℕ → ℕ) (hb : ∀ j (s : Γ((j • A).sheaf, ⊤)), s ≠ 0 →
      cartierSectionVanishingOrder (j • A) x s ≤ d j) (m : MonomialOrder (Fin n)) :
    letI : ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) := fun j =>
      geometricSmoothCartier_closedPoint_finiteDimensional_of_order_bound
        (K := K) n hn (j • A) x hClosed (d j) (hb j)
    ∃ (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ j, (cartierGradedInitialExponents A x f hf m e j).card =
          Module.finrank K Γ((j • A).sheaf, ⊤)) ∧
        ∀ j h,
          cartierGradedInitialExponents A x f hf m e j +
            cartierGradedInitialExponents A x f hf m e h ⊆
              cartierGradedInitialExponents A x f hf m e (j + h) := by
  let : ∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤) := fun j =>
    geometricSmoothCartier_closedPoint_finiteDimensional_of_order_bound
      (K := K) n hn (j • A) x hClosed (d j) (hb j)
  exact geometricSmoothCartier_closedPoint_exists_gradedExponentFamily (K := K) n hn A x hClosed m

end MixedFujita
