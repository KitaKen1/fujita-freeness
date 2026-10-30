/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltOpenImmersionLocalDescent
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.BasePointRationalKltThreshold
public import MixedFujita.HironakaSNCModelExistence

/-!
Every rational klt pullback perturbation agrees with the actual restricted pair
on a smaller base neighbourhood. Cartier pullback commutes with the actual
restriction square and the base specialization guard is reflected by the open
embedding. Hence an exact finite rational threshold is unchanged on shrinking.
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
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]


variable [hXN : IsNoetherian X] [IsIntegral Y]

include hXN

/-- Every rational klt test is preserved by actual restriction to a base neighbourhood. -/
theorem logPairIsKltOverBasePoint_rational_pullback_iff_base_open
    (g : X ⟶ Y) [IsDominant g] (η : Y) (V : Y.Opens) (hηV : η ∈ V)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y) (p q : ℕ) (hq : 1 ≤ q) :
    letI : Nonempty V := ⟨⟨η, hηV⟩⟩
    letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
    letI : (g ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ V).ι :=
      ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
    ∀ cV : EtaleChart K (g ⁻¹ᵁ V).toScheme n,
      let fV := crepantPullbackFormUnit (g ⁻¹ᵁ V).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V).ι) c f cV
      let DV := cartierPullback (g ⁻¹ᵁ V).ι D
      (LogPairIsKltOverBasePoint g η c f (q * d) (q • D + (d * p) • cartierPullback g H) ↔
        LogPairIsKltOverBasePoint (g ∣_ V) (⟨η, hηV⟩ : V.toScheme) cV fV (q * d)
          (q • DV + (d * p) • cartierPullback (g ∣_ V) (cartierPullback V.ι H))) := by
  letI : Nonempty V := ⟨⟨η, hηV⟩⟩
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  letI : (g ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ V).ι :=
    ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
  intro cV
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ V).toScheme :=
    (g ⁻¹ᵁ V).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ V).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ V).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V).ι
  have h := logPairIsKltOverBasePoint_iff_open_crepant_pullback (g ⁻¹ᵁ V).ι hj
    g η V hηV (by simpa only [Scheme.Opens.opensRange_ι] using (le_refl (g ⁻¹ᵁ V)))
    c f (q * d) (Nat.mul_pos (by omega) (by omega))
    (q • D + (d * p) • cartierPullback g H) cV
  have hdiv : cartierPullback (g ⁻¹ᵁ V).ι (q • D + (d * p) • cartierPullback g H) =
      q • cartierPullback (g ⁻¹ᵁ V).ι D +
        (d * p) • cartierPullback (g ∣_ V) (cartierPullback V.ι H) := by
    rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_nsmul,
      cartierPullback_morphismRestrict g V H]
  rw [hdiv] at h
  refine h.trans ?_
  simpa only [morphismRestrict_ι, Scheme.Opens.ι_apply] using
    logPairIsKltOverBasePoint_comp_open_immersion_iff (g ∣_ V) V.ι (⟨η, hηV⟩ : V.toScheme)
      cV (crepantPullbackFormUnit (g ⁻¹ᵁ V).ι hj c f cV) (q * d)
      (q • cartierPullback (g ⁻¹ᵁ V).ι D +
        (d * p) • cartierPullback (g ∣_ V) (cartierPullback V.ι H))

/-- Exact finite rational thresholds agree before and after shrinking the base. -/
theorem rational_klt_pullback_threshold_eq_on_base_open
    (g : X ⟶ Y) [IsDominant g] (η : Y) (V : Y.Opens) (hηV : η ∈ V)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (H : CartierDivisor Y)
    (a b q s : ℕ) (hq : 1 ≤ q) (hs : 1 ≤ s)
    (ha : ∀ (p r : ℕ), 1 ≤ r →
      (LogPairIsKltOverBasePoint g η c f (r * d) (r • D + (d * p) • cartierPullback g H) ↔
        (p : ℚ) / r < (a : ℚ) / q)) :
    letI : Nonempty V := ⟨⟨η, hηV⟩⟩
    letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
    letI : (g ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) :=
      ⟨(g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    letI : (g ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    letI : IsDominant (g ⁻¹ᵁ V).ι :=
      ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
    letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
    ∀ cV : EtaleChart K (g ⁻¹ᵁ V).toScheme n,
      let fV := crepantPullbackFormUnit (g ⁻¹ᵁ V).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V).ι) c f cV
      let DV := cartierPullback (g ⁻¹ᵁ V).ι D
      (∀ (p r : ℕ), 1 ≤ r →
        (LogPairIsKltOverBasePoint (g ∣_ V) (⟨η, hηV⟩ : V.toScheme) cV fV (r * d)
          (r • DV + (d * p) • cartierPullback (g ∣_ V) (cartierPullback V.ι H)) ↔
          (p : ℚ) / r < (b : ℚ) / s)) →
      (a : ℚ) / q = (b : ℚ) / s := by
  letI : Nonempty V := ⟨⟨η, hηV⟩⟩
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  letI : (g ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ V).ι :=
    ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
  intro cV
  dsimp only
  intro hb
  apply rational_threshold_eq_of_natural_tests a b q s hq hs
  intro p r hr
  exact (ha p r hr).symm.trans
    ((logPairIsKltOverBasePoint_rational_pullback_iff_base_open
      g η V hηV c f d hd D H p r hr cV).trans (hb p r hr))

end MixedFujita
