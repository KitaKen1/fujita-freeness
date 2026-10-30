/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SubKltLocalBasePrimeThreshold
public import MixedFujita.CanonicalBasePrimeThreshold
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
The canonical positive finite base-prime threshold for a klt pair whose boundary may have
negative coefficients. The actual local realization is unique, so the value is independent
of base neighbourhoods, equations and charts. In the effective case it agrees with the
previously constructed canonical threshold; no old definition or statement is changed.
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
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X)
  (hklt : LogPairIsKlt c f d D)

/-- The unique positive finite value supplied by an actual normalized local realization. -/
noncomputable def canonicalSubKltBasePrimeThreshold : ℚ :=
  Classical.choose (exists_localBasePrimeThresholdRealizes_of_klt g η c f d hd D hklt)

/-- The chosen value has an actual effective local Cartier and crepant-pair realization. -/
theorem canonicalSubKltBasePrimeThreshold_realizes :
    LocalBasePrimeThresholdRealizes g η c f d D
      (canonicalSubKltBasePrimeThreshold g η c f d hd D hklt) :=
  Classical.choose_spec (exists_localBasePrimeThresholdRealizes_of_klt g η c f d hd D hklt)

/-- Positivity follows from the actual finite rational endpoint construction. -/
theorem canonicalSubKltBasePrimeThreshold_pos :
    0 < canonicalSubKltBasePrimeThreshold g η c f d hd D hklt :=
  localBasePrimeThresholdRealizes_pos g η c f d D
    (canonicalSubKltBasePrimeThreshold_realizes g η c f d hd D hklt)

/-- Every actual normalized local realization computes the same canonical value. -/
theorem canonicalSubKltBasePrimeThreshold_eq_of_realizes {t : ℚ}
    (ht : LocalBasePrimeThresholdRealizes g η c f d D t) :
    canonicalSubKltBasePrimeThreshold g η c f d hd D hklt = t :=
  localBasePrimeThresholdRealizes_unique g η c f d hd D
    (canonicalSubKltBasePrimeThreshold_realizes g η c f d hd D hklt) ht

/-- The canonical scalar is characterized by geometric realization, independently of all choices. -/
theorem localBasePrimeThresholdRealizes_iff_eq_canonical_subKlt {t : ℚ} :
    LocalBasePrimeThresholdRealizes g η c f d D t ↔
      t = canonicalSubKltBasePrimeThreshold g η c f d hd D hklt := by
  constructor
  · intro ht
    exact (canonicalSubKltBasePrimeThreshold_eq_of_realizes g η c f d hd D hklt ht).symm
  · intro ht
    rw [ht]
    exact canonicalSubKltBasePrimeThreshold_realizes g η c f d hd D hklt

/-- The generalized canonical threshold agrees with the original effective-pair value. -/
theorem canonicalSubKltBasePrimeThreshold_eq_effective_canonical
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X) (heff : LogPairBoundaryEffective c f d D) :
    canonicalSubKltBasePrimeThreshold g η c f d hd D hklt =
      canonicalBasePrimeKltThreshold g η hnormX hcov c f d hd D heff hklt :=
  canonicalSubKltBasePrimeThreshold_eq_of_realizes g η c f d hd D hklt
    (canonicalBasePrimeKltThreshold_realizes g η hnormX hcov c f d hd D heff hklt)

end MixedFujita
