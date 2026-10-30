/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothClosedPointMinimizer
public import MixedFujita.AmpleSumEqualityCase
public import MixedFujita.ThresholdBaseModelLifting

/-!
The F1 minimizer and final freeness implications with closed representatives of the point loci.
Both strict volume and the equality-case order-average branch now use the closed-point
formulation. The degeneration and threshold-model inputs remain explicit and unproved.
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

/-- The minimizer data for both branches of S-NF from closed-point realization loci and (33). -/
theorem smoothMinimizerDataStatement_of_closedPoints_of_orderAverage
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hfive : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
      topologicalKrullDim X = n → 1 ≤ n →
      ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
        (c₀ : EtaleChart K X n) (A N : CartierDivisor X), CartierIsAmpleSum K A →
        CartierIsNef K N →
        (∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
            FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
              cartierRestrictedSubspaceDim K (j • A) η V) →
        ¬ (∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
          (l * (n + 1)) ^ n < r) →
        ∀ x : X, IsClosed ({x} : Set X) →
          (¬ ∃ (f : X.functionFieldˣ)
            (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) →
          ∃ σ : ℝ, (n : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
            ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K
              Γ((j • A).sheaf, ⊤),
              σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
                ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) :
    SmoothMinimizerDataStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN hnum m₀ hm₀ x hx hnf
  obtain ⟨h1, h2⟩ := hcl K X n c₀ A hA x hx
  by_cases hvol : ∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
      Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
      (l * (n + 1)) ^ n < r
  · exact ampleSum_minimizerData_of_strictVolume_closedPoints hn c₀ A hA x hx hnum hvol h1 h2 m₀
      hm₀
  · exact ampleSum_minimizerData_of_orderAverage_closedPoints hn c₀ A hA x hx hnum
      (hfive K X n hdim hn c₀ A N hA hN hnum hvol x hx hnf) h1 h2 m₀ hm₀

/-- The equality-case geometric lifting supplies (33); point loci are only required on closed points. -/
theorem smoothMinimizerDataStatement_of_closedPoints_of_equalityCaseLifting
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hlift : EqualityCaseLiftingStatement.{u}) :
    SmoothMinimizerDataStatement.{u} :=
  smoothMinimizerDataStatement_of_closedPoints_of_orderAverage hcl
    (fun K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN hnum _ x hx hnf =>
      orderAverage_of_equalityCaseLifting hlift K X n hdim hn c₀ A N hA hN hnum x hx hnf)

/-- F1 from the sum form of KV, closed-point realization loci and the geometric half of Lemma 5. -/
theorem mixedFujitaFreeness_of_kvSum_of_closedPoints_of_equalityCaseLifting
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hlift : EqualityCaseLiftingStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_minimizerData hKV
    (smoothMinimizerDataStatement_of_closedPoints_of_equalityCaseLifting hcl hlift)

/-- F1 from sum KV, closed-point realization loci, degeneration and the threshold base model. -/
theorem mixedFujitaFreeness_of_kvSum_of_closedPoints_of_thresholdBaseModel
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hmodel : ThresholdBaseModelStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_closedPoints_of_equalityCaseLifting hKV hcl
    (equalityCaseLifting_of_thresholdLifting hdeg
      (thresholdLifting_of_thresholdBaseModel hKV hmodel))

end MixedFujita
