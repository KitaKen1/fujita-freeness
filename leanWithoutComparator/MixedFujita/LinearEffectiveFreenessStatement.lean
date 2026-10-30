/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KawamataNumericalFreenessStatement

/-!
The statement of F2, linear effective freeness (step 1). Let (X, Δ) be a projective klt pair with
effective boundary over an uncountable algebraically closed field of characteristic zero, given as
for K-NF by a rational top form, r ≥ 1 and D' = r(K_X + Δ). Let D be a nef Cartier divisor and
a ≥ 1 an integer with a D - (K_X + Δ) nef and big, that is r a D - D' nef and big. F2 states that
m D is globally generated for every m ≥ a + ν(D) + 1. Under these hypotheses D is semiample by the
basepoint-free theorem, so its numerical dimension ν(D) equals its Iitaka dimension κ(D), the
exponent k with c j^k ≤ h^0(j D) for infinitely many j and h^0(j D) ≤ C (j + 1)^k for all j; the
statement is written with the Iitaka dimension, defined through the dimensions of the sections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Iitaka

variable (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- The Iitaka dimension of D is k: h^0(j D) is at least c j^k for infinitely many j and at most
C (j + 1)^k for all j. -/
def CartierIitakaDimension (D : CartierDivisor X) (k : ℕ) : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∃ᶠ j : ℕ in atTop,
    c * (j : ℝ) ^ k ≤ Module.finrank K Γ((j • D).sheaf, ⊤)) ∧
  ∃ C : ℝ, ∀ j : ℕ, (Module.finrank K Γ((j • D).sheaf, ⊤) : ℝ) ≤ C * ((j : ℝ) + 1) ^ k

end Iitaka

/-- F2, linear effective freeness: for a projective klt pair (X, Δ) with effective boundary over an
uncountable algebraically closed field of characteristic zero, a nef Cartier divisor D and an
integer a ≥ 1 with a D - (K_X + Δ) nef and big, m D is globally generated for every
m ≥ a + κ(D) + 1, where κ(D) = ν(D) under these hypotheses. -/
def LinearEffectiveFreeness : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (n : ℕ),
    topologicalKrullDim X = n → 1 ≤ n →
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) → CodimOneChartCovered n K X →
    (∃ H : CartierDivisor X, CartierIsAmpleProj K H) →
    ∀ (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (r : ℕ), 1 ≤ r →
    ∀ D' : CartierDivisor X, LogPairBoundaryEffective c₀ f₀ r D' → LogPairIsKlt c₀ f₀ r D' →
    ∀ D : CartierDivisor X, CartierIsNef K D → ∀ a : ℕ, 1 ≤ a →
      CartierIsNef K ((r * a) • D - D') → CartierIsBig K ((r * a) • D - D') →
      ∀ k : ℕ, CartierIitakaDimension K D k →
        ∀ m : ℕ, a + k + 1 ≤ m → CartierIsGloballyGenerated (m • D)

end MixedFujita
