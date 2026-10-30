/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import FCTargetDefinitions
public import MixedFujita.ComplexFujitaFreeness

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme MixedFujita

namespace FujitaPublication

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace variants

/-- The mixed variant: $K_X+\sum L_i+N$ is generated for $s\ge n+1$. -/
theorem mixed (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))]
    (c₀ : EtaleChart ℂ X n) (s : ℕ) (hs : n + 1 ≤ s)
    (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsAmpleProj ℂ (L i))
    (N : CartierDivisor X) (hN : CartierIsNef ℂ N) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N) := by
  exact mixedFujitaFreeness_complex X n hdim hn c₀ s hs L hL N hN

end variants

/-- Fujita freeness: $K_X+mL$ is generated for $m\ge n+1$. -/
theorem fujita (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))]
    (c₀ : EtaleChart ℂ X n) (L : CartierDivisor X) (hL : CartierIsAmpleProj ℂ L)
    (m : ℕ) (hm : n + 1 ≤ m) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + m • L) := by
  have h := variants.mixed X n hdim hn c₀ m hm (fun _ => L) (fun _ => hL)
    0 cartierIsNef_zero
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_zero] using h

end FujitaPublication
