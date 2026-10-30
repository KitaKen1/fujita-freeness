/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCBoundaryKlt
public import MixedFujita.NormalGloballyGeneratedKltPerturbation
public import MixedFujita.CartierGloballyGeneratedBoundaryPerturbation

/-!
Ordinary global generation on a smooth scheme gives actual signed and effective
all-model klt perturbations. Smoothness supplies stalk normality through the
actual generic fibers of its étale charts. No normality, finite linear system,
local product, geometric Jacobian estimate or klt conclusion is an extra input.
Resolution existence and crepant comparison with singular sources remain separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- An ordinarily globally generated divisor supplies an actual SNC perturbation
whose signed boundary is klt on every proper smooth birational model. -/
theorem cartierIsGloballyGenerated_exists_klt_perturbation
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (B D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X, cartierCoefficient B (x : X) < (d : ℤ)) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      (∀ x : CodimensionOnePoint X,
        cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
          if (x : X) ∈ Set.range η then 1 else 0) ∧
      LogPairIsKlt c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) :=
  normal_cartierIsGloballyGenerated_exists_klt_perturbation
    (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
    c₀ f₀ B D hD ξ hinj hξ hsnc hsupport d k hk hB

/-- With effective old coefficients the same construction gives an effective all-model klt pair. -/
theorem cartierIsGloballyGenerated_exists_effective_klt_perturbation
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (B D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ x : CodimensionOnePoint X,
      (x : X) ∉ Set.range ξ → cartierCoefficient B (x : X) = 0)
    (d k : ℕ) (hk : k < d)
    (hB : ∀ x : CodimensionOnePoint X,
      0 ≤ cartierCoefficient B (x : X) ∧ cartierCoefficient B (x : X) < (d : ℤ)) :
    ∃ (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (q : ℕ) (η : Fin q → X),
      Smooth (cartierSectionZeroSchemeι D s hs ≫ (X ↘ Spec (CommRingCat.of K))) ∧
      IsSNCFamily K n (Fin.append ξ η) ∧
      LogPairBoundaryEffective c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) ∧
      LogPairIsKlt c₀ f₀ d
        (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) +
          (B + k • cartierSectionZeroDivisor D s hs)) :=
  normal_cartierIsGloballyGenerated_exists_effective_klt_perturbation
    (smoothScheme_stalk_isIntegrallyClosed (K := K) (n := n))
    c₀ f₀ B D hD ξ hinj hξ hsnc hsupport d k hk hB

end MixedFujita
