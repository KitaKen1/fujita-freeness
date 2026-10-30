/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltPairs
public import MixedFujita.StrongNumericalFreenessStatement

/-!
The statement of K-NF (step 1). Let (Y, B) be a projective klt pair with effective Q-boundary over
an uncountable algebraically closed field of characteristic zero, n = dim Y ≥ 1: Y is a normal
integral scheme of finite type, smooth in codimension one, with a rational top form ω (so
K_Y = div ω), an integer r ≥ 1 and a Cartier divisor D = r(K_Y + B) with B ≥ 0, such that the
pair is klt. Let P be Cartier with A = P - (K_Y + B) ample, that is r P - D ample. The numerical
hypotheses are stated, as for S-NF, through the restricted sections of multiples of r A = r P - D:
A^n > (n + 1)^n means that the sections of j r A have dimension at least
((r (n + 1))^n + δ) j^n/n! for some δ > 0 and large j, and A^d · W ≥ (n + 1)^d for a proper
positive-dimensional W, the closure of a point, means that the restricted sections have dimension
at least ((r (n + 1))^d - ε) j^d/d! for every ε > 0 and large j. K-NF states that P is then
globally generated.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- K-NF: for a projective klt pair (Y, B) with effective boundary over an uncountable
algebraically closed field of characteristic zero, n = dim Y ≥ 1, and a Cartier divisor P with
A = P - (K_Y + B) ample, A^n > (n + 1)^n and A^d · W ≥ (n + 1)^d for every proper
positive-dimensional subvariety W, the divisor P is globally generated. -/
def KawamataNumericalFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (Y : Scheme.{u})
    [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim Y = n → 1 ≤ n →
    (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) → CodimOneChartCovered n K Y →
    ∀ (c₀ : EtaleChart K Y n) (f₀ : Y.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D : CartierDivisor Y, LogPairBoundaryEffective c₀ f₀ r D → LogPairIsKlt c₀ f₀ r D →
    ∀ P : CartierDivisor Y, CartierIsAmpleProj K (r • P - D) →
      (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j : ℕ in atTop,
        ((((r * (n + 1) : ℕ) : ℝ) ^ n + δ) * (j : ℝ) ^ n / n.factorial ≤
          cartierRestrictedDim K (j • (r • P - D)) (genericPoint Y))) →
      (∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d → d < n →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop,
          ((((r * (n + 1) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedDim K (j • (r • P - D)) η)) →
      CartierIsGloballyGenerated P

end MixedFujita
