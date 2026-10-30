/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierBigDefinition
public import MixedFujita.CartierSectionBertini
public import MixedFujita.CanonicalDivisor
public import MixedFujita.CartierDivisorCoefficients
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-!
The statement of Kawamata–Viehweg vanishing in the form used in section 6.3 of the manuscript
(step 10: the statement only, the theorem itself is not proved here).

Let T be a smooth proper variety of dimension n over the field K, ξ_1, …, ξ_r distinct prime
divisors of T in simple normal crossing position with member divisors E_k, Q a Cartier divisor,
m ≥ 1 and a_k < m natural numbers such that the Cartier divisor

  m (Q − K_T) − Σ a_k E_k

is nef and big; that is, Q − (K_T + Σ (a_k/m) E_k) is nef and big, with a boundary whose
coefficients lie in [0, 1) and whose support has simple normal crossings. The statement is that
H¹(T, O_T(Q)) = 0. In characteristic zero this is a case of the vanishing theorem of Kawamata
and Viehweg.

A second form is stated for a sum m (Q − K_T) − Σ a_k E_k = D₁ + D₂ with D₁ nef and big and D₂
nef. Such a sum is nef and big, so this is again a case of the vanishing theorem; the bigness of
the sum of a nef and big divisor and a nef divisor is not proved in this development, which is why
the sum form is a separate statement. It implies the first form.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Kawamata–Viehweg vanishing in degree one for a fractional simple normal crossing boundary on
smooth proper varieties of dimension n over K: if m (Q − K_T) − Σ a_k E_k is nef and big with
0 ≤ a_k < m, then H¹(T, O_T(Q)) = 0. -/
def KawamataViehwegVanishingSNC (K : Type u) [Field K] (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
    Function.Injective ξ → (∀ k, Order.coheight (ξ k) = 1) → IsSNCFamily K n ξ →
    ∀ E : Fin r → CartierDivisor T,
      (∀ (k : Fin r) (z : CodimensionOnePoint T),
        cartierCoefficient (E k) (z : T) = if (z : T) = ξ k then 1 else 0) →
    ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r → ℕ, (∀ k, a k < m) →
      CartierIsNef K (m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k) →
      CartierIsBig K (m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k) →
      Subsingleton (Scheme.Modules.Cohomology Q.sheaf 1)

/-- Kawamata–Viehweg vanishing in degree one in the sum form: if
m (Q − K_T) − Σ a_k E_k = D₁ + D₂ with 0 ≤ a_k < m, D₁ nef and big and D₂ nef, then
H¹(T, O_T(Q)) = 0. -/
def KawamataViehwegVanishingSNCSum (K : Type u) [Field K] (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))] (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
    Function.Injective ξ → (∀ k, Order.coheight (ξ k) = 1) → IsSNCFamily K n ξ →
    ∀ E : Fin r → CartierDivisor T,
      (∀ (k : Fin r) (z : CodimensionOnePoint T),
        cartierCoefficient (E k) (z : T) = if (z : T) = ξ k then 1 else 0) →
    ∀ (Q : CartierDivisor T) (m : ℕ), 1 ≤ m → ∀ a : Fin r → ℕ, (∀ k, a k < m) →
    ∀ D₁ D₂ : CartierDivisor T,
      m • (Q - smoothCanonicalDivisor cT) - ∑ k, a k • E k = D₁ + D₂ →
      CartierIsNef K D₁ → CartierIsBig K D₁ → CartierIsNef K D₂ →
      Subsingleton (Scheme.Modules.Cohomology Q.sheaf 1)

/-- The sum form of the Kawamata–Viehweg statement implies the form for one nef and big
divisor. -/
theorem kawamataViehwegVanishingSNC_of_sum {K : Type u} [Field K] {n : ℕ}
    (h : KawamataViehwegVanishingSNCSum K n) : KawamataViehwegVanishingSNC K n := by
  intro T _ _ _ _ _ cT r ξ hinj hξ hsnc E hEc Q m hm a ha hnef hbig
  exact h T cT r ξ hinj hξ hsnc E hEc Q m hm a ha _ 0 (add_zero _).symm hnef hbig cartierIsNef_zero

end MixedFujita
