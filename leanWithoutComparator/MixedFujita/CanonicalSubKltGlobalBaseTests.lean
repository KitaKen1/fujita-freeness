/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeGlobalEquation
public import MixedFujita.CanonicalSubKltBasePrimeLocalTests
public import MixedFujita.RationalThresholdBaseOpenRestriction

/-!
The canonical local threshold is computed by a global Cartier divisor of coefficient one
as soon as that divisor is effective on a neighbourhood of the base prime. It need not be
effective on the entire base. Actual open-restriction tests identify the global and local
intervals, retaining the rational top form and the original denominator.
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
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)

/-- Every global normalized Cartier divisor effective near the prime computes its canonical
local klt threshold. Global effectivity is not required. -/
theorem canonicalSubKltBasePrimeThreshold_global_klt_tests
    (U : Y.Opens) (hηU : (η : Y) ∈ U) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : IsDominant U.ι :=
      ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    ∀ (H : CartierDivisor Y), cartierCoefficient H (η : Y) = 1 →
      (cartierPullback U.ι H).IsEffective → ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint g (η : Y) c f (q * d)
          (q • D + (d * p) • cartierPullback g H) ↔
            (p : ℚ) / q < canonicalSubKltBasePrimeThreshold g η c f d hd D hklt) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : IsDominant U.ι :=
    ⟨U.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  intro H hHη heff p q hq
  obtain ⟨cU⟩ := exists_etaleChart_on_integral_open_immersion (g ⁻¹ᵁ U).ι c
  have hnorm : cartierCoefficient (cartierPullback U.ι H)
      (⟨(η : Y), hηU⟩ : U.toScheme) = 1 :=
    (cartierPullback_base_open_coefficient_at_normal_prime η U hηU H).trans hHη
  have hlocal := canonicalSubKltBasePrimeThreshold_local_tests g η c f d hd D hklt
    U hηU (cartierPullback U.ι H) heff hnorm cU p q hq
  exact (logPairIsKltOverBasePoint_rational_pullback_iff_base_open g (η : Y) U hηU
    c f d hd D H p q hq cU).trans hlocal.1

end MixedFujita
