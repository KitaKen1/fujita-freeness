/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SubKltBasePrimeRationalThreshold
public import MixedFujita.LocalBasePrimeThresholdRealization
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.KltNonproperBirationalTests

/-!
Positive finite local threshold realizations for arbitrary klt pairs. The boundary may have
negative coefficients. All reference charts, normalized effective base equations and exact
klt/lc intervals are constructed internally; neither source normality nor a codimension-one
chart cover is an extra input. Uniqueness uses the existing independent-neighbourhood theorem.
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


variable [IsIntegral Y] [IsLocallyNoetherian Y]

variable (g : X ⟶ Y) [IsDominant g] [hgp : IsProper g]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X)
  (hklt : LogPairIsKlt c f d D)

include hgp hd hklt

/-- Every prescribed effective normalized base equation has an actual finite klt/lc endpoint. -/
theorem exists_rational_klt_lc_threshold_on_given_base_open_of_klt
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
  have hkltU := logPairIsKlt_crepant_pullback_without_properness (g ⁻¹ᵁ U).ι hj
    c f d hd D hklt cU
  obtain ⟨a, q₀, ha, hq₀, hpos, hlc, hnot, T, hTi, hTo, hTN, hTs, ρ, hdom,
    hover, hprop, hρ, cT, t, hguard, hGpos, hratio, hendpoint, htest⟩ :=
    exists_exact_rational_klt_threshold_over_base_prime_of_klt (g ∣_ U) ⟨θ, hθ⟩
      cU _ d hd (cartierPullback (g ⁻¹ᵁ U).ι D) hkltU H hH (by rw [hHη]; norm_num)
  exact ⟨a, q₀, ha, hq₀, htest⟩

/-- A klt pair has an actual positive finite normalized local realization, allowing a
negative boundary. All local choices are supplied by the construction. -/
theorem exists_localBasePrimeThresholdRealizes_of_klt :
    ∃ t : ℚ, LocalBasePrimeThresholdRealizes g η c f d D t := by
  obtain ⟨U, -, hηU, H, hH, hHη⟩ :=
    normal_base_prime_effective_cartier_neighborhood η ⊤ (by trivial)
  letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U.1) := dominant_preimage_nonempty g U.1
  letI : (g ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U.1).ι :=
    ⟨(g ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U.1) := isDominant_morphismRestrict_integral g U.1
  obtain ⟨cU⟩ := exists_etaleChart_on_integral_open_immersion (g ⁻¹ᵁ U.1).ι c
  obtain ⟨a, q₀, ha, hq₀, htest⟩ :=
    exists_rational_klt_lc_threshold_on_given_base_open_of_klt g η c f d hd D hklt
      U.1 hηU H hH hHη cU
  exact ⟨(a : ℚ) / q₀, a, q₀, ha, hq₀, rfl, U.1, hηU, H, cU, hH, hHη, htest⟩

/-- The positive finite local endpoint is unique without any boundary-effectivity input. -/
theorem existsUnique_localBasePrimeThresholdRealizes_of_klt :
    ∃! t : ℚ, LocalBasePrimeThresholdRealizes g η c f d D t := by
  obtain ⟨t, ht⟩ := exists_localBasePrimeThresholdRealizes_of_klt g η c f d hd D hklt
  exact ⟨t, ht, fun s hs => localBasePrimeThresholdRealizes_unique g η c f d hd D hs ht⟩

end MixedFujita
