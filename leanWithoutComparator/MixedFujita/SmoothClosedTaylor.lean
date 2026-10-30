/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothClosedPoints
public import MixedFujita.SmoothRelativeCoordinates
public import MixedFujita.SmoothCartierTaylor

/-!
Actual Cartier sections at algebraically closed closed points have injective
Taylor maps without a supplied stalk evaluation or completion isomorphism.
Smooth relative dimension n fixes the number of variables to Fin n.
Local equations exist by the actual Cartier divisor API and can be chosen.
Projective section finite dimensionality and dim X comparisons are not claimed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

theorem smoothRelativeScheme_closedPoint_exists_stalkCoordinates [IsAlgClosed K] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (x : X) (hClosed : IsClosed {x}) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  let := SmoothOfRelativeDimension.smooth n (X ↘ Spec (CommRingCat.of K))
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hClosed
  exact smoothRelativeScheme_rationalPoint_exists_stalkCoordinates n x β

variable [IsIntegral X]

theorem smoothCartier_closedPoint_exists_injectiveTaylor [IsAlgClosed K]
    [Smooth (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    ∃ n : ℕ, ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
      ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
        cartierSectionVanishingOrder D x s := by
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hClosed
  exact smoothCartier_exists_injectiveTaylor D x β f hf

theorem smoothRelativeCartier_exists_injectiveTaylor (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (x : X) (β : X.presheaf.stalk x →ₐ[K] K)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
      ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
        cartierSectionVanishingOrder D x s := by
  let := SmoothOfRelativeDimension.smooth n (X ↘ Spec (CommRingCat.of K))
  let : IsNoetherianRing (X.presheaf.stalk x) := smoothScheme_stalk_isNoetherianRing (K := K) x
  obtain ⟨e, _⟩ := smoothRelativeScheme_rationalPoint_exists_stalkCoordinates n x β
  exact ⟨e, cartierTaylorCoordinates_injective D x f hf e,
    cartierTaylorCoordinates_order_eq_vanishingOrder D x f hf e⟩

theorem smoothRelativeCartier_closedPoint_exists_injectiveTaylor [IsAlgClosed K] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
      ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
        cartierSectionVanishingOrder D x s := by
  let := SmoothOfRelativeDimension.smooth n (X ↘ Spec (CommRingCat.of K))
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hClosed
  exact smoothRelativeCartier_exists_injectiveTaylor n D x β f hf

theorem smoothRelativeCartier_closedPoint_exists_TaylorData [IsAlgClosed K] (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x}) :
    ∃ (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
        ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
          cartierSectionVanishingOrder D x s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  obtain ⟨e, hi, ho⟩ :=
    smoothRelativeCartier_closedPoint_exists_injectiveTaylor (K := K) n D x hClosed f hf
  exact ⟨f, hf, e, hi, ho⟩

end MixedFujita
