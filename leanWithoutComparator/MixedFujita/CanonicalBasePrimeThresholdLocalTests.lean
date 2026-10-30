/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeThreshold
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
Every actual normalized effective Cartier equation on every base neighbourhood
has the canonical rational klt/lc threshold. Construct its finite endpoint from
the actual restricted pair, then identify the value by neighbourhood-independent
uniqueness. This transfers lc endpoint tests without a general lc open-source
restriction theorem.
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
  (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
  (hklt : LogPairIsKlt c f d D)

include hgp hnorm hcov hd heff hklt

/-- Every prescribed effective normalized base equation has an actual finite klt/lc endpoint. -/
theorem exists_rational_klt_lc_threshold_on_given_base_open
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
      ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q < (a : ℚ) / q₀) ∧
        (LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q ≤ (a : ℚ) / q₀) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
  letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U).ι :=
    ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
  intro H hH hHη cU
  haveI : IsProper (g ∣_ U) := inferInstance
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U).toScheme :=
    (g ⁻¹ᵁ U).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ U).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ U).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι
  let θ : U.toScheme := ⟨(η : Y), hηU⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective U.ι θ
      (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap θ))).trans η.property
  have heffU := logPairBoundaryEffective_open_crepant_pullback (g ⁻¹ᵁ U).ι hj
    hnorm hcov c f d D heff cU
  have hkltU := logPairIsKlt_crepant_pullback_without_properness (g ⁻¹ᵁ U).ι hj
    c f d hd D hklt cU
  obtain ⟨heffall, a, q₀, ha, hq₀, hpos, hlc, hnot, T, hTi, hTo, hTN, hTs, ρ, hdom,
    hover, hprop, hρ, cT, t, hguard, hGpos, hratio, hendpoint, htest⟩ :=
    exists_exact_rational_klt_threshold_over_base_prime (g ∣_ U) ⟨θ, hθ⟩
      cU _ d hd (cartierPullback (g ⁻¹ᵁ U).ι D) heffU hkltU H hH (by rw [hHη]; norm_num)
  exact ⟨a, q₀, ha, hq₀, htest⟩

/-- All actual normalized local equations compute the same canonical klt/lc interval. -/
theorem canonicalBasePrimeKltThreshold_local_tests
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
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q < canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt) ∧
        (LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q ≤ canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt) := by
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
  obtain ⟨a, q₀, ha, hq₀, htest⟩ := exists_rational_klt_lc_threshold_on_given_base_open
    g η hnorm hcov c f d hd D heff hklt U hηU H hH hHη cU
  have hr : LocalBasePrimeThresholdRealizes g η c f d D ((a : ℚ) / q₀) :=
    ⟨a, q₀, ha, hq₀, rfl, U, hηU, H, cU, hH, hHη, htest⟩
  have heq := canonicalBasePrimeKltThreshold_eq_of_realizes g η hnorm hcov c f d hd D heff hklt hr
  intro p q hq
  simpa only [heq] using htest p q hq

/-- At a positive integral presentation of the canonical endpoint, every normalized
local pair is log canonical and fails klt. -/
theorem canonicalBasePrimeKltThreshold_local_endpoint
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
      canonicalBasePrimeKltThreshold g η hnorm hcov c f d hd D heff hklt = (a : ℚ) / q₀ →
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
  obtain ⟨hkt, hlc⟩ := canonicalBasePrimeKltThreshold_local_tests
    g η hnorm hcov c f d hd D heff hklt U hηU H hH hHη cU a q₀ hq₀
  refine ⟨hlc.mpr heq.symm.le, ?_⟩
  intro h
  have hbad := hkt.mp h
  rw [heq] at hbad
  exact lt_irrefl _ hbad

end MixedFujita
