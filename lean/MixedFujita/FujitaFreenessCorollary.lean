/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataViehwegCharZero
public import MixedFujita.CartierNefDefinition

/-!
The case L_1 = ⋯ = L_m = L of F1 (step 14).

F1 (`MixedFujitaFreeness`, proved in check 558 as `mixedFujitaFreeness_proved`) with all the
ample divisors equal to one ample divisor L gives: on a smooth projective variety of dimension
n ≥ 1 over an uncountable algebraically closed field of characteristic zero, K_X + m L + N is
globally generated for every m ≥ n + 1 and every nef N (`fujitaFreenessNef_proved`); with N = 0
this is the form of Fujita's freeness statement (`FujitaFreeness`, `fujitaFreeness_proved`).
The statement uses the same definitions as F1: `CartierIsAmpleProj` (a positive multiple is
linearly equivalent to a hyperplane section of a closed embedding into projective space),
`CartierIsNef` (nonnegative degree on every smooth proper curve mapping to X),
`smoothCanonicalDivisor` (the divisor of the top form of an étale chart) and
`CartierIsGloballyGenerated` (at every point some global section of O(D) has a unit local
coefficient).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

attribute [local instance] cartierBaseOpenAlgebra

/-- The case of F1 with all ample divisors equal: for an ample divisor L on a smooth projective
variety of dimension n ≥ 1 over an uncountable algebraically closed field of characteristic
zero, K_X + m L is globally generated for every m ≥ n + 1. -/
def FujitaFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (L : CartierDivisor X), CartierIsAmpleProj K L → ∀ m : ℕ, n + 1 ≤ m →
        CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + m • L)

/-- **K_X + m L + N is globally generated for m ≥ n + 1, L ample and N nef**, from F1 with
L_1 = ⋯ = L_m = L. -/
theorem fujitaFreenessNef_proved (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    [Uncountable K] (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
    (L : CartierDivisor X) (hL : CartierIsAmpleProj K L) (m : ℕ) (hm : n + 1 ≤ m)
    (N : CartierDivisor X) (hN : CartierIsNef K N) :
    CartierIsGloballyGenerated (smoothCanonicalDivisor c₀ + m • L + N) := by
  have h := mixedFujitaFreeness_proved K X n hdim hn c₀ m hm (fun _ => L) (fun _ => hL) N hN
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h

/-- F1 implies the statement `FujitaFreeness` (take N = 0). -/
theorem fujitaFreeness_of_mixedFujitaFreeness (h : MixedFujitaFreeness.{u}) :
    FujitaFreeness.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ c₀ L hL m hm
  have h1 := h K X n hdim hn c₀ m hm (fun _ => L) (fun _ => hL) 0 cartierIsNef_zero
  rwa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_zero] at h1

/-- **The statement `FujitaFreeness` holds.** -/
theorem fujitaFreeness_proved : FujitaFreeness.{u} :=
  fujitaFreeness_of_mixedFujitaFreeness mixedFujitaFreeness_proved

end MixedFujita
