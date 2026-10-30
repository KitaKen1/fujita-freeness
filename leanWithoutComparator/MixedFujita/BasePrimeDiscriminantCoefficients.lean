/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeThresholdLocalTests
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
The canonical rational discriminant coefficient family on a normal base is
one minus the positive local threshold. Every coefficient is below one and
the family is uniquely characterized by actual local threshold realizations.
Finite support and nonnegativity have not been proved here; this construction
is a function on prime divisors and does not yet construct a Weil divisor.
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

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [IsNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]


variable [IsIntegral Y] [IsLocallyNoetherian Y]

variable (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- Rational discriminant coefficients; finite support is a separate geometric obligation. -/
noncomputable def basePrimeDiscriminantCoefficients : CodimensionOnePoint Y → ℚ :=
  fun η =>
    letI := hnormY (η : Y)
    1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt

/-- The coefficient uses the original pair's canonical threshold at the same base prime. -/
theorem basePrimeDiscriminantCoefficients_apply (η : CodimensionOnePoint Y) :
    letI := hnormY (η : Y)
    basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η =
      1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt := rfl

/-- The strict upper bound comes from positivity of the actual local threshold. -/
theorem basePrimeDiscriminantCoefficients_lt_one (η : CodimensionOnePoint Y) :
    basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η < 1 := by
  letI := hnormY (η : Y)
  change 1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt < 1
  have h := canonicalBasePrimeKltThreshold_pos g η hnorm hcov c f d hd D heff hklt
  linarith

/-- Vanishing of the coefficient is exactly the threshold-one condition. -/
theorem basePrimeDiscriminantCoefficients_eq_zero_iff (η : CodimensionOnePoint Y) :
    letI := hnormY (η : Y)
    basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η = 0 ↔
      canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1 := by
  letI := hnormY (η : Y)
  change 1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 0 ↔ _
  constructor <;> intro h <;> linarith

/-- Any actual local threshold realization computes the coefficient. -/
theorem basePrimeDiscriminantCoefficients_eq_of_realizes
    (η : CodimensionOnePoint Y) (t : ℚ)
    (ht : letI := hnormY (η : Y)
      LocalBasePrimeThresholdRealizes g η c f d D t) :
    basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt η = 1 - t := by
  letI := hnormY (η : Y)
  change 1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = 1 - t
  rw [canonicalBasePrimeKltThreshold_eq_of_realizes g η hnorm hcov c f d hd D heff hklt ht]

/-- Local geometric realizations uniquely determine the full rational coefficient family. -/
theorem basePrimeDiscriminantCoefficients_unique (b : CodimensionOnePoint Y → ℚ)
    (hb : ∀ (η : CodimensionOnePoint Y), letI := hnormY (η : Y)
      LocalBasePrimeThresholdRealizes g η c f d D (1 - b η)) :
    b = basePrimeDiscriminantCoefficients g hnormY hnorm hcov c f d hd D heff hklt := by
  funext η
  letI := hnormY (η : Y)
  have heq := canonicalBasePrimeKltThreshold_eq_of_realizes g η hnorm hcov c f d hd D heff hklt (hb η)
  change b η = 1 - canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt
  linarith

end MixedFujita
