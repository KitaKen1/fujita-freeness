/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizationSetsPrincipalShift
public import MixedFujita.HyperplaneSumVeryAmple
public import MixedFujita.ProjectiveAmpleMinimizerData
public import MixedFujita.StrongNumericalFreenessConditional

/-!
The data of the minimizer for an ample sum (steps 11 and 14, assembly).

Let A be an ample sum on a smooth variety Y of dimension m over an uncountable algebraically
closed field of characteristic zero, with zero boundary, and let x be a closed point. A positive
multiple l A is linearly equivalent to the hyperplane divisor J of a closed immersion cut by a
coordinate that does not vanish at x (`cartierIsAmpleProj_exists_hyperplane_nonvanishing`). The
sections of D J and of (D l) A have the same dimension, and the realization sets of j J are closed
when those of (j l) A are. So the data of the minimizer exist at x for every m₀ ≥ 1 from:
* the numerical hypothesis for A;
* the strict volume inequality A^m > (m + 1)^m, stated through the multiples: for every l ≥ 1, if
  h⁰((D l) A)/D^m tends to r/m!, then (l (m + 1))^m < r;
* the closedness of the realization sets of A, in the tuple and in the point, at all large degrees.

Hence the minimizer statement used by S-NF for ample sums, and with it F1 (given the sum form of
the Kawamata–Viehweg statement), follows from the closedness of the realization sets of ample sums
at closed points and from the data of the minimizer when the volume inequality is not strict (the
equality case, Lemma 5 of the manuscript).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer at a closed point x for an ample sum A, with zero boundary, for every
m₀ ≥ 1, from the numerical hypothesis for A, the strict volume inequality A^m > (m + 1)^m (through
the multiples D l A) and the closedness of the realization sets of A in the tuple and in the point
at all large degrees. -/
theorem ampleSum_kltIsolationMinimizerData_of_strictVolume (hm : 1 ≤ m) (cY : EtaleChart K Y m)
    (A : CartierDivisor Y) (hA : CartierIsAmpleSum K A) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hvol : ∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
        Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop (𝓝 ((r : ℝ) / m.factorial)) →
        (l * (m + 1)) ^ m < r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • A) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  obtain ⟨l, hl, n, e, hci, he, g, hg, hggen, hgx, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing (cartierIsAmpleProj_of_isAmpleSum hA) x
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  refine projectiveHyperplane_ample_kltIsolationMinimizerData_of_strictVolume e g hg hggen he hm
    cY A hl φ hlA x hxc hgx hgrow ?_ ?_ ?_ m₀ hm₀
  · intro r hr
    refine hvol l hl r (Tendsto.congr (fun D => ?_) hr)
    rw [finrank_nsmul_eq_of_nsmul_eq (K := K) hlA D]
  · filter_upwards [htend.eventually hclosed] with j hj
    exact realizationSetsZariskiClosed_of_nsmul_eq cY _ 1 _ hlA x j hj
  · filter_upwards [htend.eventually hclosedPt] with j hj
    exact normalizedProfiles_isClosed_of_nsmul_eq cY _ 1 _ hlA j hj

end Assembly

/-- The minimizer statement used by S-NF for ample sums follows from the closedness of the
realization sets of ample sums at closed points (in the tuple and in the point, at all large
degrees) and from the data of the minimizer when the volume inequality is not strict. -/
theorem smoothMinimizerDataStatement_of_closed_of_notStrict
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hnotStrict : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
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
        ∀ m₀ : ℕ, 1 ≤ m₀ → ∀ x : X, IsClosed ({x} : Set X) →
          (¬ ∃ (f : X.functionFieldˣ)
            (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) →
          KltIsolationMinimizerData c₀ (1 : X.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
            A m₀ x) :
    SmoothMinimizerDataStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN hnum m₀ hm₀ x hx hnf
  by_cases hvol : ∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
      Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
      (l * (n + 1)) ^ n < r
  · obtain ⟨h1, h2⟩ := hcl K X n c₀ A hA x hx
    exact ampleSum_kltIsolationMinimizerData_of_strictVolume hn c₀ A hA x hx hnum hvol h1 h2 m₀
      hm₀
  · exact hnotStrict K X n hdim hn c₀ A N hA hN hnum hvol m₀ hm₀ x hx hnf

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, and the data of the
minimizer when the volume inequality is not strict. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_notStrict
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
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hnotStrict : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
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
        ∀ m₀ : ℕ, 1 ≤ m₀ → ∀ x : X, IsClosed ({x} : Set X) →
          (¬ ∃ (f : X.functionFieldˣ)
            (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) →
          KltIsolationMinimizerData c₀ (1 : X.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
            A m₀ x) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_minimizerData hKV
    (smoothMinimizerDataStatement_of_closed_of_notStrict hcl hnotStrict)

end MixedFujita
