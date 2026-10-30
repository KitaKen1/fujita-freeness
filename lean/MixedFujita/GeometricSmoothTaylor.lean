/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothClosedTaylor
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

/-!
For an actual smooth irreducible scheme of geometric Krull dimension n,
the relative dimension is derived, rather than supplied. At algebraically
closed closed points this constructs centered etale affine charts and
actual stalk completion coordinates in exactly Fin n variables. Integral
Cartier sections then have injective Taylor maps preserving intrinsic order.
Projective finite dimensionality and the higher geometric inputs are separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
  [IrreducibleSpace X]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

theorem geometricSmoothScheme_relativeDimension (n : ℕ) (hn : topologicalKrullDim X = n) :
    SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K)) :=
  TauCeti.AlgebraicGeometry.smoothOfRelativeDimension_of_topologicalKrullDim_eq
    (X ↘ Spec (CommRingCat.of K)) hn

include K in
theorem geometricSmoothScheme_closedPoint_stalk_dimension (n : ℕ)
    (hn : topologicalKrullDim X = n) (x : X) (hClosed : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = n :=
  (TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    (X ↘ Spec (CommRingCat.of K)) hClosed).trans hn

theorem geometricSmoothScheme_rationalPoint_exists_stalkCoordinates (n : ℕ)
    (hn : topologicalKrullDim X = n) (x : X) (β : X.presheaf.stalk x →ₐ[K] K) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  exact smoothRelativeScheme_rationalPoint_exists_stalkCoordinates n x β

theorem geometricSmoothScheme_closedPoint_exists_stalkCoordinates [IsAlgClosed K] (n : ℕ)
    (hn : topologicalKrullDim X = n) (x : X) (hClosed : IsClosed {x}) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  exact smoothRelativeScheme_closedPoint_exists_stalkCoordinates (K := K) n x hClosed

theorem geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart [IsAlgClosed K]
    (n : ℕ) (hn : topologicalKrullDim X = n) (x : X) (hClosed : IsClosed {x}) :
    ∃ (U : X.Opens) (_hU : IsAffineOpen U) (hx : x ∈ U)
      (β : X.presheaf.stalk x →ₐ[K] K) (g : MvPolynomial (Fin n) K →ₐ[K] Γ(X, U)),
      g.Etale ∧ ∀ p, rationalAffineGermPoint x hx β (g p) = MvPolynomial.constantCoeff p := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  obtain ⟨U, hU, hx, hs⟩ := smoothRelativeScheme_exists_affineStandardSmooth (K := K) n x
  let := hs
  let β := smoothAffineClosedPointEvaluation (K := K) hU x hx hClosed
  obtain ⟨g, hg, hc⟩ :=
    standardSmoothRelativeDimension_exists_centeredEtaleChart n (rationalAffineGermPoint x hx β)
  exact ⟨U, hU, hx, β, g, hg, hc⟩

variable [IsIntegral X]

theorem geometricSmoothCartier_closedPoint_exists_injectiveTaylor [IsAlgClosed K] (n : ℕ)
    (hn : topologicalKrullDim X = n) (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x})
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
      ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
        cartierSectionVanishingOrder D x s := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  exact smoothRelativeCartier_closedPoint_exists_injectiveTaylor (K := K) n D x hClosed f hf

theorem geometricSmoothCartier_closedPoint_exists_TaylorData [IsAlgClosed K] (n : ℕ)
    (hn : topologicalKrullDim X = n) (D : CartierDivisor X) (x : X) (hClosed : IsClosed {x}) :
    ∃ (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
      ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        Function.Injective (cartierTaylorCoordinates D x f hf e) ∧
        ∀ s, (cartierTaylorCoordinates D x f hf e s).order =
          cartierSectionVanishingOrder D x s := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  exact smoothRelativeCartier_closedPoint_exists_TaylorData (K := K) n D x hClosed

end MixedFujita
