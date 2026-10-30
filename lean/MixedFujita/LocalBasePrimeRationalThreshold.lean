/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BasePrimeRationalKltThreshold
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.HironakaSNCModelExistence

/-!
From the original proper dominant map and effective klt pair, construct an
actual affine base neighbourhood, its coefficient-one Cartier equation, the
actual effective klt restricted pair and its attained finite rational klt/lc
threshold. No base Cartier equation, restricted pair, SNC model, positive test
prime or threshold certificate is supplied as an additional input.
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

/-- Construct the original contraction's local generic-prime threshold, inside
any prescribed base neighbourhood, with all actual geometric data internal. -/
theorem exists_local_base_prime_exact_rational_threshold
    (g : X ⟶ Y) [IsDominant g] [IsProper g]
    (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) (W : Y.Opens) (hηW : (η : Y) ∈ W) :
    ∃ (V : Y.affineOpens), V.1 ≤ W ∧ ∃ (hηV : (η : Y) ∈ V.1),
      letI : Nonempty V.1 := ⟨⟨(η : Y), hηV⟩⟩
      letI : Nonempty (g ⁻¹ᵁ V.1) := dominant_preimage_nonempty g V.1
      letI : (g ⁻¹ᵁ V.1).toScheme.Over (Spec (CommRingCat.of K)) :=
        ⟨(g ⁻¹ᵁ V.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
      letI : (g ⁻¹ᵁ V.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      letI : IsDominant (g ⁻¹ᵁ V.1).ι :=
        ⟨(g ⁻¹ᵁ V.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
      letI : IsDominant (g ∣_ V.1) := isDominant_morphismRestrict_integral g V.1
      let θ : V.1.toScheme := ⟨(η : Y), hηV⟩
      ∃ (H : CartierDivisor V.1.toScheme) (cV : EtaleChart K (g ⁻¹ᵁ V.1).toScheme n),
        let fV := crepantPullbackFormUnit (g ⁻¹ᵁ V.1).ι
          (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V.1).ι) c f cV
        let DV := cartierPullback (g ⁻¹ᵁ V.1).ι D
        Order.coheight θ = 1 ∧ H.IsEffective ∧ cartierCoefficient H θ = 1 ∧
        LogPairBoundaryEffective cV fV d DV ∧ LogPairIsKlt cV fV d DV ∧
        (∀ (p q : ℕ), 1 ≤ q →
          LogPairBoundaryEffective cV fV (q * d) (q • DV + (d * p) • (cartierPullback (g ∣_ V.1) H))) ∧
        ∃ (a q₀ : ℕ), 1 ≤ a ∧ 1 ≤ q₀ ∧ 0 < (a : ℚ) / q₀ ∧
          LogPairIsLogCanonicalOverBasePoint (g ∣_ V.1) θ cV fV (q₀ * d) (q₀ • DV + (d * a) • (cartierPullback (g ∣_ V.1) H)) ∧
          (¬ LogPairIsKltOverBasePoint (g ∣_ V.1) θ cV fV (q₀ * d) (q₀ • DV + (d * a) • (cartierPullback (g ∣_ V.1) H))) ∧
          ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (ρ : T ⟶ (g ⁻¹ᵁ V.1).toScheme) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
            (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
            (cT : EtaleChart K T n) (t : CodimensionOnePoint T),
            θ ∈ closure ({(ρ ≫ (g ∣_ V.1)) (t : T)} : Set V.1.toScheme) ∧
            0 < cartierCoefficient (cartierPullback ρ (cartierPullback (g ∣_ V.1) H)) (t : T) ∧
            (a : ℚ) / q₀ =
              ((d : ℚ) - cartierCoefficient
                (crepantBoundaryCartier ρ hρ cV fV d DV cT etaleCharts_cover) (t : T)) /
                ((d : ℚ) * cartierCoefficient (cartierPullback ρ (cartierPullback (g ∣_ V.1) H)) (t : T)) ∧
            cartierCoefficient (logDiscrepancyDivisor n ρ hρ cV fV (q₀ * d)
              (q₀ • DV + (d * a) • (cartierPullback (g ∣_ V.1) H)) cT etaleCharts_cover) (t : T) = -((q₀ * d : ℕ) : ℤ) ∧
            ∀ (p q : ℕ), 1 ≤ q →
              (LogPairIsKltOverBasePoint (g ∣_ V.1) θ cV fV (q * d) (q • DV + (d * p) • (cartierPullback (g ∣_ V.1) H)) ↔
                (p : ℚ) / q < (a : ℚ) / q₀) ∧
              (LogPairIsLogCanonicalOverBasePoint (g ∣_ V.1) θ cV fV (q * d) (q • DV + (d * p) • (cartierPullback (g ∣_ V.1) H)) ↔
                (p : ℚ) / q ≤ (a : ℚ) / q₀) := by
  obtain ⟨V, hVW, hηV, H, hH, hHη⟩ := normal_base_prime_effective_cartier_neighborhood η W hηW
  letI : Nonempty V.1 := ⟨⟨(η : Y), hηV⟩⟩
  letI : Nonempty (g ⁻¹ᵁ V.1) := dominant_preimage_nonempty g V.1
  letI : (g ⁻¹ᵁ V.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ V.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ V.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ V.1).ι :=
    ⟨(g ⁻¹ᵁ V.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ V.1) := isDominant_morphismRestrict_integral g V.1
  haveI : IsProper (g ∣_ V.1) := inferInstance
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ V.1).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ V.1).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ V.1).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ V.1).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ V.1).toScheme :=
    (g ⁻¹ᵁ V.1).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ V.1).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  let θ : V.1.toScheme := ⟨(η : Y), hηV⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective V.1.ι θ
      (ConcreteCategory.bijective_of_isIso (V.1.ι.stalkMap θ))).trans η.property
  obtain ⟨cV, heffV, hkltV⟩ := exists_effective_klt_crepant_open_pullback
    (g ⁻¹ᵁ V.1).ι hnorm hcov c f d hd D heff hklt
  refine ⟨V, hVW, hηV, H, cV, hθ, hH, hHη, heffV, hkltV, ?_⟩
  exact exists_exact_rational_klt_threshold_over_base_prime (g ∣_ V.1) ⟨θ, hθ⟩
    cV _ d hd (cartierPullback (g ⁻¹ᵁ V.1).ι D) heffV hkltV H hH (by rw [hHη]; norm_num)

end MixedFujita
