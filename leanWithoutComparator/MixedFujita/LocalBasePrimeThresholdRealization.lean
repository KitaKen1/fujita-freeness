/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalBasePrimeThresholdIndependence
public import MixedFujita.LocalBasePrimeRationalThreshold
public import MixedFujita.CommonBaseOpenRefinement
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.BasePointRationalKltThreshold
public import MixedFujita.HironakaSNCModelExistence

/-!
Positive finite local threshold realizations retain actual base opens, effective
coefficient-one Cartier equations and the original pair's crepant restriction.
All rational klt and lc tests are part of a realization. Existence is supplied
by the proved geometric construction; uniqueness compares independently chosen
neighbourhoods using their internally constructed common refinement.
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

variable {K : Type u} [Field K] {n : ℕ} {X Y : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [IsIntegral Y] [IsLocallyNoetherian Y]

/-- A positive finite rational endpoint realized by actual normalized local klt/lc tests. -/
def LocalBasePrimeThresholdRealizes (g : X ⟶ Y) [IsDominant g]
    (η : CodimensionOnePoint Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) (t : ℚ) : Prop :=
  ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ t = (a : ℚ) / q₀ ∧
  ∃ (U : Y.Opens) (hηU : (η : Y) ∈ U),
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : Nonempty (g ⁻¹ᵁ U) := dominant_preimage_nonempty g U
    letI : (g ⁻¹ᵁ U).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ U).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ U).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ U).ι :=
      ⟨(g ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ U) := isDominant_morphismRestrict_integral g U
    ∃ (H : CartierDivisor U.toScheme) (cU : EtaleChart K (g ⁻¹ᵁ U).toScheme n),
      let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U).ι) c f cU
      let DU := cartierPullback (g ⁻¹ᵁ U).ι D
      H.IsEffective ∧ cartierCoefficient H (⟨(η : Y), hηU⟩ : U.toScheme) = 1 ∧
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme) cU fU (q * d)
          (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q < t) ∧
        (LogPairIsLogCanonicalOverBasePoint (g ∣_ U) (⟨(η : Y), hηU⟩ : U.toScheme)
          cU fU (q * d) (q • DU + (d * p) • cartierPullback (g ∣_ U) H) ↔ (p : ℚ) / q ≤ t)

/-- Every positive finite realization has a strictly positive value. -/
theorem localBasePrimeThresholdRealizes_pos (g : X ⟶ Y) [IsDominant g]
    (η : CodimensionOnePoint Y) (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor X) {t : ℚ}
    (h : LocalBasePrimeThresholdRealizes g η c f d D t) : 0 < t := by
  obtain ⟨a, q₀, ha, hq₀, rfl, _⟩ := h
  exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hq₀)

variable [CharZero K] [IsNoetherian X]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- The original effective klt pair supplies an actual local threshold realization. -/
theorem exists_localBasePrimeThresholdRealizes (g : X ⟶ Y) [IsDominant g] [IsProper g]
    (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) :
    ∃ t : ℚ, LocalBasePrimeThresholdRealizes g η c f d D t := by
  obtain ⟨U, hUtop, hηU, H, cU, hθ, hH, hHη, heffU, hkltU, heffall,
    a, q₀, ha, hq₀, hpos, hlc, hnot, T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ,
    cT, t, hguard, hGpos, hratio, hendpoint, htest⟩ :=
    exists_local_base_prime_exact_rational_threshold g η hnorm hcov c f d hd D heff hklt ⊤ (by trivial)
  letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U.1) := dominant_preimage_nonempty g U.1
  letI : (g ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U.1).ι :=
    ⟨(g ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U.1) := isDominant_morphismRestrict_integral g U.1
  exact ⟨(a : ℚ) / q₀, a, q₀, ha, hq₀, rfl, U.1, hηU, H, cU, hH, hHη, htest⟩

/-- Different actual neighbourhoods, equations and charts cannot realize different endpoints. -/
theorem localBasePrimeThresholdRealizes_unique (g : X ⟶ Y) [IsDominant g]
    (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) {t s : ℚ}
    (ht : LocalBasePrimeThresholdRealizes g η c f d D t)
    (hs : LocalBasePrimeThresholdRealizes g η c f d D s) : t = s := by
  obtain ⟨a, q₀, ha, hq₀, hta, U₁, hη₁, h₁⟩ := ht
  obtain ⟨b, q₁, hb, hq₁, hsb, U₂, hη₂, h₂⟩ := hs
  letI : Nonempty U₁ := ⟨⟨(η : Y), hη₁⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U₁) := dominant_preimage_nonempty g U₁
  letI : (g ⁻¹ᵁ U₁).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U₁).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U₁).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U₁).ι :=
    ⟨(g ⁻¹ᵁ U₁).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U₁) := isDominant_morphismRestrict_integral g U₁
  letI : Nonempty U₂ := ⟨⟨(η : Y), hη₂⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U₂) := dominant_preimage_nonempty g U₂
  letI : (g ⁻¹ᵁ U₂).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U₂).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U₂).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U₂).ι :=
    ⟨(g ⁻¹ᵁ U₂).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U₂) := isDominant_morphismRestrict_integral g U₂
  obtain ⟨H₁, c₁, hH₁, hcoef₁, htest₁⟩ := h₁
  obtain ⟨H₂, c₂, hH₂, hcoef₂, htest₂⟩ := h₂
  have heq := local_base_prime_rational_threshold_independent_of_neighborhood
    g η U₁ U₂ hη₁ hη₂ c f d hd D H₁ H₂ c₁ c₂ hcoef₁ hcoef₂
    a b q₀ q₁ hq₀ hq₁
    (fun p r hr => by simpa only [hta] using (htest₁ p r hr).1)
    (fun p r hr => by simpa only [hsb] using (htest₂ p r hr).1)
  exact hta.trans (heq.trans hsb.symm)

/-- There is a unique positive finite local threshold value, without any supplied local data. -/
theorem existsUnique_localBasePrimeThresholdRealizes (g : X ⟶ Y) [IsDominant g] [IsProper g]
    (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) :
    ∃! t : ℚ, LocalBasePrimeThresholdRealizes g η c f d D t := by
  obtain ⟨t, ht⟩ := exists_localBasePrimeThresholdRealizes g η hnorm hcov c f d hd D heff hklt
  exact ⟨t, ht, fun s hs => localBasePrimeThresholdRealizes_unique g η c f d hd D hs ht⟩

end MixedFujita
