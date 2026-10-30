/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalThresholdOpenSquare
public import MixedFujita.CommonBaseOpenRefinement
public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.BasePointRationalKltThreshold
public import MixedFujita.HironakaSNCModelExistence

/-!
Independently chosen base neighbourhoods give identical rational klt tests at a
normal base prime. Construct their actual intersection, open maps and a common
reference chart internally. Pull both coefficient-one Cartier divisors to that
intersection and compare through actual stalk isomorphisms. Exact finite local
thresholds therefore agree, including different local equations and charts.
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


variable [hXN : IsNoetherian X] [IsIntegral Y] [IsLocallyNoetherian Y]

include hXN

/-- Two independently chosen actual neighbourhoods and coefficient-one equations
have identical rational klt tests; the common refinement is constructed. -/
theorem local_base_prime_rational_klt_tests_independent_of_neighborhood
    (g : X ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
    [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (U₁ U₂ : Y.Opens) (hη₁ : (η : Y) ∈ U₁) (hη₂ : (η : Y) ∈ U₂)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) :
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
    ∀ (H₁ : CartierDivisor U₁.toScheme) (H₂ : CartierDivisor U₂.toScheme)
      (c₁ : EtaleChart K (g ⁻¹ᵁ U₁).toScheme n) (c₂ : EtaleChart K (g ⁻¹ᵁ U₂).toScheme n),
      let f₁ := crepantPullbackFormUnit (g ⁻¹ᵁ U₁).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₁).ι) c f c₁
      let f₂ := crepantPullbackFormUnit (g ⁻¹ᵁ U₂).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₂).ι) c f c₂
      let D₁ := cartierPullback (g ⁻¹ᵁ U₁).ι D
      let D₂ := cartierPullback (g ⁻¹ᵁ U₂).ι D
      cartierCoefficient H₁ (⟨(η : Y), hη₁⟩ : U₁.toScheme) = 1 →
      cartierCoefficient H₂ (⟨(η : Y), hη₂⟩ : U₂.toScheme) = 1 →
      ∀ (p q : ℕ), 1 ≤ q →
        (LogPairIsKltOverBasePoint (g ∣_ U₁) (⟨(η : Y), hη₁⟩ : U₁.toScheme) c₁ f₁ (q * d)
          (q • D₁ + (d * p) • cartierPullback (g ∣_ U₁) H₁) ↔
        LogPairIsKltOverBasePoint (g ∣_ U₂) (⟨(η : Y), hη₂⟩ : U₂.toScheme) c₂ f₂ (q * d)
          (q • D₂ + (d * p) • cartierPullback (g ∣_ U₂) H₂)) := by
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
  intro H₁ H₂ c₁ c₂
  dsimp only
  intro hH₁ hH₂ p q hq
  let V : Y.Opens := U₁ ⊓ U₂
  have hηV : (η : Y) ∈ V := ⟨hη₁, hη₂⟩
  letI : Nonempty V := ⟨⟨(η : Y), hηV⟩⟩
  letI : Nonempty (g ⁻¹ᵁ V) := dominant_preimage_nonempty g V
  letI : (g ⁻¹ᵁ V).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  haveI : (g ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ V).ι :=
    ⟨(g ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ V) := isDominant_morphismRestrict_integral g V
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U₁).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U₁).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U₁).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U₁).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U₁).toScheme :=
    (g ⁻¹ᵁ U₁).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ U₁).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U₂).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U₂).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U₂).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U₂).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U₂).toScheme :=
    (g ⁻¹ᵁ U₂).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ U₂).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
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
  obtain ⟨cV⟩ := exists_etaleChart_on_integral_open_immersion (g ⁻¹ᵁ V).ι c
  let θ : V.toScheme := ⟨(η : Y), hηV⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective V.ι θ
      (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap θ))).trans η.property
  letI : IsDiscreteValuationRing (V.toScheme.presheaf.stalk θ) :=
    normal_base_prime_open_stalk_DVR η V hηV
  letI : IsIntegrallyClosed (V.toScheme.presheaf.stalk θ) := inferInstance
  let b₁ := Y.homOfLE (show V ≤ U₁ from inf_le_left)
  let a₁ := X.homOfLE (g.preimage_mono (show V ≤ U₁ from inf_le_left))
  letI : IsDominant b₁ := isDominant_homOfLE_integral _
  letI : IsDominant a₁ := isDominant_homOfLE_integral _
  haveI : a₁.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change a₁ ≫ ((g ⁻¹ᵁ U₁).ι ≫ (X ↘ Spec (CommRingCat.of K))) =
      (g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have ha₁ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) a₁) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion a₁
  have hj₁ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ U₁).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₁).ι
  have hpoint₁ : b₁ θ = (⟨(η : Y), hη₁⟩ : U₁.toScheme) := Subtype.ext (by simp [b₁, θ])
  have hform₁ := crepantPullbackFormUnit_comp (g ⁻¹ᵁ U₁).ι a₁ hj₁ ha₁ c f c₁ cV
  have hform₁' : crepantPullbackFormUnit a₁ ha₁ c₁
      (crepantPullbackFormUnit (g ⁻¹ᵁ U₁).ι hj₁ c f c₁) cV =
      crepantPullbackFormUnit (g ⁻¹ᵁ V).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V).ι) c f cV := by
    simpa only [a₁, Scheme.homOfLE_ι] using hform₁.symm
  have hD₁ : cartierPullback a₁ (cartierPullback (g ⁻¹ᵁ U₁).ι D) =
      cartierPullback (g ⁻¹ᵁ V).ι D := by
    rw [← cartierPullback_comp]
    simpa only [a₁, Scheme.homOfLE_ι]
  let b₂ := Y.homOfLE (show V ≤ U₂ from inf_le_right)
  let a₂ := X.homOfLE (g.preimage_mono (show V ≤ U₂ from inf_le_right))
  letI : IsDominant b₂ := isDominant_homOfLE_integral _
  letI : IsDominant a₂ := isDominant_homOfLE_integral _
  haveI : a₂.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change a₂ ≫ ((g ⁻¹ᵁ U₂).ι ≫ (X ↘ Spec (CommRingCat.of K))) =
      (g ⁻¹ᵁ V).ι ≫ (X ↘ Spec (CommRingCat.of K))
    rw [← Category.assoc, Scheme.homOfLE_ι]
  have ha₂ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) a₂) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion a₂
  have hj₂ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (g ⁻¹ᵁ U₂).ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₂).ι
  have hpoint₂ : b₂ θ = (⟨(η : Y), hη₂⟩ : U₂.toScheme) := Subtype.ext (by simp [b₂, θ])
  have hform₂ := crepantPullbackFormUnit_comp (g ⁻¹ᵁ U₂).ι a₂ hj₂ ha₂ c f c₂ cV
  have hform₂' : crepantPullbackFormUnit a₂ ha₂ c₂
      (crepantPullbackFormUnit (g ⁻¹ᵁ U₂).ι hj₂ c f c₂) cV =
      crepantPullbackFormUnit (g ⁻¹ᵁ V).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ V).ι) c f cV := by
    simpa only [a₂, Scheme.homOfLE_ι] using hform₂.symm
  have hD₂ : cartierPullback a₂ (cartierPullback (g ⁻¹ᵁ U₂).ι D) =
      cartierPullback (g ⁻¹ᵁ V).ι D := by
    rw [← cartierPullback_comp]
    simpa only [a₂, Scheme.homOfLE_ι]
  let H := cartierPullback b₁ H₁
  have hcoeff : cartierCoefficient (cartierPullback b₂ H₂) θ = cartierCoefficient H θ := by
    rw [cartierCoefficient_homOfLE_at_normal_base_prime η _ hηV hη₂,
      cartierCoefficient_homOfLE_at_normal_base_prime η _ hηV hη₁, hH₁, hH₂]
  have h₁ := logPairIsKltOverBasePoint_rational_pullback_iff_open_square_coefficient
    a₁ ha₁ b₁ (g ∣_ U₁) (g ∣_ V)
    (morphismRestrict_homOfLE g V U₁ inf_le_left).symm
    (morphismRestrict_homOfLE_range_cover g inf_le_left) ⟨θ, hθ⟩ c₁
    (crepantPullbackFormUnit (g ⁻¹ᵁ U₁).ι hj₁ c f c₁) d hd
    (cartierPullback (g ⁻¹ᵁ U₁).ι D) H₁ H (by rfl) cV p q hq
  rw [hform₁', hD₁] at h₁
  simp only [hpoint₁] at h₁
  have h₂ := logPairIsKltOverBasePoint_rational_pullback_iff_open_square_coefficient
    a₂ ha₂ b₂ (g ∣_ U₂) (g ∣_ V)
    (morphismRestrict_homOfLE g V U₂ inf_le_right).symm
    (morphismRestrict_homOfLE_range_cover g inf_le_right) ⟨θ, hθ⟩ c₂
    (crepantPullbackFormUnit (g ⁻¹ᵁ U₂).ι hj₂ c f c₂) d hd
    (cartierPullback (g ⁻¹ᵁ U₂).ι D) H₂ H hcoeff cV p q hq
  rw [hform₂', hD₂] at h₂
  simp only [hpoint₂] at h₂
  exact h₁.trans h₂.symm

/-- The two exact finite local thresholds are equal, with no common chart or refinement input. -/
theorem local_base_prime_rational_threshold_independent_of_neighborhood
    (g : X ⟶ Y) [IsDominant g] (η : CodimensionOnePoint Y)
    [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]
    (U₁ U₂ : Y.Opens) (hη₁ : (η : Y) ∈ U₁) (hη₂ : (η : Y) ∈ U₂)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) :
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
    ∀ (H₁ : CartierDivisor U₁.toScheme) (H₂ : CartierDivisor U₂.toScheme)
      (c₁ : EtaleChart K (g ⁻¹ᵁ U₁).toScheme n) (c₂ : EtaleChart K (g ⁻¹ᵁ U₂).toScheme n),
      let f₁ := crepantPullbackFormUnit (g ⁻¹ᵁ U₁).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₁).ι) c f c₁
      let f₂ := crepantPullbackFormUnit (g ⁻¹ᵁ U₂).ι
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U₂).ι) c f c₂
      let D₁ := cartierPullback (g ⁻¹ᵁ U₁).ι D
      let D₂ := cartierPullback (g ⁻¹ᵁ U₂).ι D
      cartierCoefficient H₁ (⟨(η : Y), hη₁⟩ : U₁.toScheme) = 1 →
      cartierCoefficient H₂ (⟨(η : Y), hη₂⟩ : U₂.toScheme) = 1 →
      ∀ (a b q s : ℕ), 1 ≤ q → 1 ≤ s →
      (∀ (p r : ℕ), 1 ≤ r →
        (LogPairIsKltOverBasePoint (g ∣_ U₁) (⟨(η : Y), hη₁⟩ : U₁.toScheme) c₁ f₁ (r * d)
          (r • D₁ + (d * p) • cartierPullback (g ∣_ U₁) H₁) ↔ (p : ℚ) / r < (a : ℚ) / q)) →
      (∀ (p r : ℕ), 1 ≤ r →
        (LogPairIsKltOverBasePoint (g ∣_ U₂) (⟨(η : Y), hη₂⟩ : U₂.toScheme) c₂ f₂ (r * d)
          (r • D₂ + (d * p) • cartierPullback (g ∣_ U₂) H₂) ↔ (p : ℚ) / r < (b : ℚ) / s)) →
      (a : ℚ) / q = (b : ℚ) / s := by
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
  intro H₁ H₂ c₁ c₂
  dsimp only
  intro hH₁ hH₂ a b q s hq hs ha hb
  apply rational_threshold_eq_of_natural_tests a b q s hq hs
  intro p r hr
  exact (ha p r hr).symm.trans
    ((local_base_prime_rational_klt_tests_independent_of_neighborhood
      g η U₁ U₂ hη₁ hη₂ c f d hd D H₁ H₂ c₁ c₂ hH₁ hH₂ p r hr).trans (hb p r hr))

end MixedFujita
