/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FujitaFreenessCorollary
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Cardinality

/-!
F1 and its case L_1 = ⋯ = L_m = L over the complex numbers, as in the manuscript (step 14).

The field hypotheses of F1 (algebraically closed, characteristic zero, uncountable) hold for ℂ;
ℂ is uncountable because ℝ is (`complex_uncountable`). So on a smooth projective complex variety
of dimension n ≥ 1, K_X + L_1 + ⋯ + L_s + N is globally generated for ample L_i, s ≥ n + 1 and
nef N (`mixedFujitaFreeness_complex`), and K_X + m L is globally generated for ample L and
m ≥ n + 1 (`fujitaFreeness_complex`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

attribute [local instance] cartierBaseOpenAlgebra

/-- The complex numbers are uncountable. -/
theorem complex_uncountable : Uncountable ℂ := Complex.ofReal_injective.uncountable

/-- **F1 over the complex numbers**: on a smooth projective complex variety of dimension
n ≥ 1, K_X + L_1 + ⋯ + L_s + N is globally generated for ample L_1, …, L_s with s ≥ n + 1 and
nef N. -/
theorem mixedFujitaFreeness_complex (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))] (c₀ : EtaleChart ℂ X n) (s : ℕ)
    (hs : n + 1 ≤ s) (L : Fin s → CartierDivisor X) (hL : ∀ i, CartierIsAmpleProj ℂ (L i))
    (N : CartierDivisor X) (hN : CartierIsNef ℂ N) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + ∑ i, L i + N) :=
  haveI := complex_uncountable
  mixedFujitaFreeness_proved.{0} ℂ X n hdim hn c₀ s hs L hL N hN

/-- **The case L_1 = ⋯ = L_m = L of F1 over the complex numbers**: K_X + m L is globally
generated for an ample L on a smooth projective complex variety of dimension n ≥ 1 and every
m ≥ n + 1. -/
theorem fujitaFreeness_complex (X : Scheme.{0}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of ℂ))] (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of ℂ))] (c₀ : EtaleChart ℂ X n)
    (L : CartierDivisor X) (hL : CartierIsAmpleProj ℂ L) (m : ℕ) (hm : n + 1 ≤ m) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + m • L) :=
  haveI := complex_uncountable
  fujitaFreeness_proved.{0} ℂ X n hdim hn c₀ L hL m hm

end MixedFujita
