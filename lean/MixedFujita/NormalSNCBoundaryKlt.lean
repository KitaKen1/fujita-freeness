/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ActualSNCJacobianBound

/-!
A signed SNC Cartier boundary with coefficients below its clearing denominator is
klt on every actual proper smooth birational model. The local product and the
geometric Jacobian inequality are constructed by the preceding modules.
Normality of the source stalks remains explicit. Resolution existence, the
singular-source crepant comparison and smooth-to-normality are separate work.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

/-- SNC configuration and signed coefficients<d give actual all-model klt.
No geometric discrepancy or Jacobian-sum inequality is supplied as a hypothesis.
The source's stalk normality is still stated explicitly. -/
theorem normal_isSNCFamily_logPairIsKlt
    (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (B : CartierDivisor X) {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ z : CodimensionOnePoint X,
      (z : X) ∉ Set.range ξ → cartierCoefficient B (z : X) = 0)
    (hb : ∀ i, cartierCoefficient B (ξ i) < (d : ℤ)) :
    LogPairIsKlt c₀ f₀ d
      (d • (smoothCanonicalDivisor c₀ + principalCartierDivisor X f₀) + B) := by
  intro T _ _ _ _ ρ _ _ _ hρ c'₀ t ht
  exact normal_isSNCFamily_discrepancy_bound_of_jacobian_sum ρ hρ hnorm c₀ f₀ d hd B
    ξ hinj hξ hsnc hsupport hb c'₀ ⟨t, ht⟩
    (fun c σ hc hcsnc c' hc' =>
      actual_snc_coordinate_sum_le_jacobian ρ hρ ⟨t, ht⟩ c hc ξ σ hcsnc c' hc')

end MixedFujita
