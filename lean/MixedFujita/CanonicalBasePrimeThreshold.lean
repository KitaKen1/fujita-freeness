/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalBasePrimeThresholdRealization
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
The canonical positive rational local threshold at a normal base prime.
Choose a value only after proving existence of actual local klt/lc realizations;
comparison of independently chosen neighbourhoods proves it is the only value.
This is a scalar threshold, not a finitely supported discriminant divisor.
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
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

/-- The unique positive finite value supplied by an actual normalized local realization. -/
noncomputable def canonicalBasePrimeKltThreshold : ℚ :=
  Classical.choose (exists_localBasePrimeThresholdRealizes g η hnorm hcov c f d hd D heff hklt)

/-- The chosen value has an actual effective local Cartier and crepant-pair realization. -/
theorem canonicalBasePrimeKltThreshold_realizes :
    LocalBasePrimeThresholdRealizes g η c f d D
      (canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt) :=
  Classical.choose_spec (exists_localBasePrimeThresholdRealizes g η hnorm hcov c f d hd D heff hklt)

/-- Positivity follows from the actual finite rational endpoint construction. -/
theorem canonicalBasePrimeKltThreshold_pos :
    0 < canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt :=
  localBasePrimeThresholdRealizes_pos g η c f d D
    (canonicalBasePrimeKltThreshold_realizes g η hnorm hcov c f d hd D heff hklt)

/-- Every actual normalized local realization computes the same canonical value. -/
theorem canonicalBasePrimeKltThreshold_eq_of_realizes {t : ℚ}
    (ht : LocalBasePrimeThresholdRealizes g η c f d D t) :
    canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = t :=
  localBasePrimeThresholdRealizes_unique g η c f d hd D
    (canonicalBasePrimeKltThreshold_realizes g η hnorm hcov c f d hd D heff hklt) ht

/-- The canonical scalar is characterized by geometric realization, independently of all choices. -/
theorem localBasePrimeThresholdRealizes_iff_eq_canonical {t : ℚ} :
    LocalBasePrimeThresholdRealizes g η c f d D t ↔
      t = canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt := by
  constructor
  · intro ht
    exact (canonicalBasePrimeKltThreshold_eq_of_realizes g η hnorm hcov c f d hd D heff hklt ht).symm
  · intro ht
    rw [ht]
    exact canonicalBasePrimeKltThreshold_realizes g η hnorm hcov c f d hd D heff hklt

end MixedFujita
