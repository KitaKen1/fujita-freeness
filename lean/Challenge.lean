/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FCTargetDefinitions

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme MixedFujita

namespace FujitaPublication

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Fujita freeness: $K_X+mL$ is generated for $m\ge n+1$. -/
theorem fujita (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))]
    (c₀ : EtaleChart ℂ X n) (L : CartierDivisor X) (hL : CartierIsAmpleProj ℂ L)
    (m : ℕ) (hm : n + 1 ≤ m) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + m • L) := by
  sorry

namespace variants

/-- The mixed variant: $K_X+\sum L_i+N$ is generated for $s\ge n+1$. -/
theorem mixed (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))]
    (c₀ : EtaleChart ℂ X n) (s : ℕ) (hs : n + 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsAmpleProj ℂ (L i))
    (N : CartierDivisor X) (hN : CartierIsNef ℂ N) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N) := by
  sorry

end variants

end FujitaPublication
