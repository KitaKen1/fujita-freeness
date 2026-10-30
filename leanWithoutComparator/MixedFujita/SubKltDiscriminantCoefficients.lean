/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalSubKltBasePrimeLocalTests
public import MixedFujita.BasePrimeDiscriminantCoefficients

/-!
Canonical rational discriminant coefficients for sub-klt presentations, allowing negative
source boundary coefficients. Positivity of the local threshold gives the strict upper
bound one. Nonnegativity and finite support are not inferred for this generalized family;
in the effective case its coefficients agree with the original construction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

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
  [IsIntegral Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [IsDominant g] [IsProper g]
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)

/-- The canonical coefficient family is defined for klt pairs with possibly negative boundary. -/
noncomputable def subKltBasePrimeDiscriminantCoefficients : CodimensionOnePoint Y → ℚ :=
  fun η =>
    letI := hnormY (η : Y)
    1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt

/-- Each coefficient is one minus the unique actual normalized local threshold. -/
theorem subKltBasePrimeDiscriminantCoefficients_apply (η : CodimensionOnePoint Y) :
    letI := hnormY (η : Y)
    subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η =
      1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt := rfl

/-- Generalized discriminant coefficients are strictly below one; no lower bound is assumed. -/
theorem subKltBasePrimeDiscriminantCoefficients_lt_one (η : CodimensionOnePoint Y) :
    subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η < 1 := by
  letI := hnormY (η : Y)
  change 1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt < 1
  have h := canonicalSubKltBasePrimeThreshold_pos g η c f d hd D hklt
  linarith

/-- Vanishing of the generalized coefficient is exactly the threshold-one condition. -/
theorem subKltBasePrimeDiscriminantCoefficients_eq_zero_iff (η : CodimensionOnePoint Y) :
    letI := hnormY (η : Y)
    subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η = 0 ↔
      canonicalSubKltBasePrimeThreshold g η c f d hd D hklt = 1 := by
  letI := hnormY (η : Y)
  change 1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt = 0 ↔ _
  constructor <;> intro h <;> linarith

/-- With an effective original boundary the entire generalized family agrees with the
previously constructed coefficient family, preserving all original choices and statements. -/
theorem subKltBasePrimeDiscriminantCoefficients_eq_effective
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (heff : LogPairBoundaryEffective c f d D) :
    subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt =
      basePrimeDiscriminantCoefficients g hnormY hnormX hcov c f d hd D heff hklt := by
  funext η
  letI := hnormY (η : Y)
  change 1 - canonicalSubKltBasePrimeThreshold g η c f d hd D hklt =
    1 - canonicalBasePrimeKltThreshold g η hnormX hcov c f d hd D heff hklt
  rw [canonicalSubKltBasePrimeThreshold_eq_effective_canonical g η c f d hd D hklt
    hnormX hcov heff]

end MixedFujita
