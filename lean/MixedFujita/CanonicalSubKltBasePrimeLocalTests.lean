/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalSubKltBasePrimeThreshold
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
Every normalized effective local base equation computes the canonical sub-klt threshold,
even when the source boundary has negative coefficients. The endpoint is log canonical
and fails klt, with the original local equation, form and denominator retained.
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

variable (g : X ⟶ Y) [IsDominant g] [hgp : IsProper g]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X)
  (hklt : LogPairIsKlt c f d D)

include hgp hd hklt

/-- All actual normalized local equations compute the same canonical klt/lc interval. -/
theorem canonicalSubKltBasePrimeThreshold_local_tests
    (U : Y.Opens) (hηU : (η : Y) ∈ U) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
    letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ U).ι :=
      ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
    ∀ (H : CartierDivisor U.toScheme) (_ : H.IsEffective)
      (_ : cartierCoefficient H (⟨(η : Y), hηU⟩ : U.toScheme) = 1)
      (cU : EtaleChart K (g ⁻¹ᵁ U).toScheme n),
      let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι) c f cU
      let DU := cartierPullback (g ⁻¹ᵁ U).ι D
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q < canonicalSubKltBasePrimeThreshold g η c f d hd D hklt) ∧
        (LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q ≤ canonicalSubKltBasePrimeThreshold g η c f d hd D hklt) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  intro H hH hHη cU
  dsimp only
  obtain ⟨a, q₀, ha, hq₀, htest⟩ := exists_rational_klt_lc_threshold_on_given_base_open_of_klt
    g η c f d hd D hklt U hηU H hH hHη cU
  have hr : LocalBasePrimeThresholdRealizes g η c f d D ((a : ℚ) / q₀) :=
    ⟨a, q₀, ha, hq₀, rfl, U, hηU, H, cU, hH, hHη, htest⟩
  have heq := canonicalSubKltBasePrimeThreshold_eq_of_realizes g η c f d hd D hklt hr
  intro p q hq
  simpa only [heq] using htest p q hq

/-- At a positive integral presentation of the canonical endpoint, every normalized
local pair is log canonical and fails klt. -/
theorem canonicalSubKltBasePrimeThreshold_local_endpoint
    (U : Y.Opens) (hηU : (η : Y) ∈ U) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
    letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ U).ι :=
      ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
    ∀ (H : CartierDivisor U.toScheme) (_ : H.IsEffective)
      (_ : cartierCoefficient H (⟨(η : Y), hηU⟩ : U.toScheme) = 1)
      (cU : EtaleChart K (g ⁻¹ᵁ U).toScheme n),
      let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι) c f cU
      let DU := cartierPullback (g ⁻¹ᵁ U).ι D
      ∀ (a q₀ : ℕ), 1 ≤ a → 1 ≤ q₀ →
      canonicalSubKltBasePrimeThreshold g η c f d hd D hklt = (a : ℚ) / q₀ →
      LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q₀ * d)
        (q₀ • DU + (d * a) • cartierPullback (g ∣_ U) H) ∧
      ¬ LogPairIsKltOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q₀ * d)
        (q₀ • DU + (d * a) • cartierPullback (g ∣_ U) H) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  intro H hH hHη cU
  dsimp only
  intro a q₀ ha hq₀ heq
  obtain ⟨hkt, hlc⟩ := canonicalSubKltBasePrimeThreshold_local_tests
    g η c f d hd D hklt U hηU H hH hHη cU a q₀ hq₀
  refine ⟨hlc.mpr heq.symm.le, ?_⟩
  intro h
  have hbad := hkt.mp h
  rw [heq] at hbad
  exact lt_irrefl _ hbad

end MixedFujita
