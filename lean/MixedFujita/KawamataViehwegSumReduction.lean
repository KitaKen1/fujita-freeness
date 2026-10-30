/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KodairaLemmaStatementProof
public import MixedFujita.RealizationConstructible

/-!
The sum form of the Kawamata–Viehweg statement from the usual form (step 10).

`KawamataViehwegVanishingSNCSum` (used for F1) asks for H¹(T, O(Q)) = 0 when
m (Q − K_T) − Σ a_k E_k = D₁ + D₂ with D₁ nef and big and D₂ nef. Since D₁ + D₂ is nef, this is
the usual form `KawamataViehwegVanishingSNC` applied to D₁ + D₂ as soon as D₁ + D₂ is big:
`BigAddNefStatement` (a big plus a nef divisor is big, on smooth proper varieties; a standard
consequence of Kodaira's lemma and Kleiman's criterion, extended to proper varieties by Chow's
lemma) (`kawamataViehwegVanishingSNCSum_of_bigAddNef`). Hence F1 follows from the usual
Kawamata–Viehweg statement (the one used for F2), `BigAddNefStatement`, Lemma 3 at closed points,
the local constructibility of the realization sets in the point, the degenerate form of Lemma 3
and the local statement
(`mixedFujitaFreeness_of_kawamataViehweg_of_bigAddNef_of_lemmaThree_of_constructible`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- A big plus a nef Cartier divisor is big, on smooth proper varieties of dimension n over K. -/
def BigAddNefStatement (K : Type u) [Field K] (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) [IsIntegral T] [IsLocallyNoetherian T] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    [IsProper (T ↘ Spec (CommRingCat.of K))] (D₁ D₂ : CartierDivisor T),
    CartierIsNef K D₁ → CartierIsBig K D₁ → CartierIsNef K D₂ → CartierIsBig K (D₁ + D₂)

/-- The sum form of the Kawamata–Viehweg statement from the usual form and "big plus nef is
big". -/
theorem kawamataViehwegVanishingSNCSum_of_bigAddNef {K : Type u} [Field K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n) (hba : BigAddNefStatement K n) :
    KawamataViehwegVanishingSNCSum K n := by
  intro T _ _ _ _ _ cT r ξ hinj hξ hsnc E hEc Q m hm a ha D₁ D₂ heq hnef₁ hbig₁ hnef₂
  apply hKV T cT r ξ hinj hξ hsnc E hEc Q m hm a ha
  · rw [heq]
    exact cartierIsNef_add hnef₁ hnef₂
  · rw [heq]
    exact hba T D₁ D₂ hnef₁ hbig₁ hnef₂

/-- F1 from the usual Kawamata–Viehweg statement, "big plus nef is big", Lemma 3 at closed points,
the local constructibility of the realization sets in the point, the degenerate form of Lemma 3
and the local statement with the fixed part of the base ideal. -/
theorem mixedFujitaFreeness_of_kawamataViehweg_of_bigAddNef_of_lemmaThree_of_constructible
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hptc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsLocallyConstructible {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hmodel : ThresholdBaseModelStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_lemmaThree_of_constructible
    (fun K _ _ _ n => kawamataViehwegVanishingSNCSum_of_bigAddNef (hKV K n) (hba K n))
    hlct hptc hdeg hmodel

end MixedFujita
