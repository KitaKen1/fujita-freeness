/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantRoundupExceptionalDifference
public import MixedFujita.EffectiveKltOpenRestriction
public import MixedFujita.KltNonproperBirationalTests

/-!
Apply actual roundup normalization and rational section comparison to the
same fixed SNC source, to further proper crepant models and to actual open
restrictions. The open restriction uses effective klt normalization and does
not require a new SNC family on the open scheme. Nearby base-section lattices
are preserved by the same comparison.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Tower

variable {K : Type u} [Field K] {n : ℕ} {X S T : Scheme.{u}}
  [IsIntegral X] [IsIntegral S] [IsIntegral T] [IsNoetherian S] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [S.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (S ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (π : S ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (ρ : T ⟶ S) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- A further actual proper crepant model preserves every rational section
lattice of the roundup on the fixed SNC source. Normalization is internal. -/
theorem snc_crepant_tower_roundup_mem_sections_iff
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cS : EtaleChart K S n) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → S) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ s : CodimensionOnePoint S, (s : S) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover) (s : S) = 0)
    (E₀ : CartierDivisor S) (heff : E₀.IsEffective)
    (hE₀ : ∀ s : CodimensionOnePoint S, cartierCoefficient E₀ (s : S) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover)
        (s : S) : ℝ) / (d : ℝ))⌉)
    (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (ρ ≫ π)
        (dominantFunctionFieldAlgHom_comp_bijective π ρ hπ hρ) c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (U : S.Opens) [Nonempty U] (z : S.functionField) :
    letI := dominant_preimage_nonempty ρ U
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom z) ∈ E₁.sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := S) U).symm z ∈ E₀.sections U := by
  letI : Smooth (S ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s) :=
    fun s => smooth_stalk_isIntegrallyClosed (K := K) s
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcovS : CodimOneChartCovered n K S := by
    intro s _
    exact Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S) (n := n)).symm ▸ Opens.mem_top s)
  obtain ⟨hEffN, hKltN⟩ := crepant_source_roundup_normalized_pair_effective_klt
    π hπ hnormS c f d hd D cS ξ hinj hξ hsnc hsupport E₀ heff hE₀
  have hE₁' : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ cS
        (crepantPullbackFormUnit π hπ c f cS) d (cartierPullback π D)
        cT etaleCharts_cover) (t : T) : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hE₁ t, crepantBoundaryCartier_comp π ρ hπ hρ]
  exact crepant_roundup_mem_sections_iff_on_open ρ hρ hnormS hnormT hcovS cS
    (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) E₀ hEffN hKltN
    cT E₁ hE₁' U z

end Tower

section OpenRefinement

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {S Z T : Scheme.{u}}
  [IsIntegral S] [IsIntegral Z] [IsIntegral T]
  [IsLocallyNoetherian S] [IsLocallyNoetherian Z] [IsNoetherian T]
  [S.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of K))]
  [IsSeparated (S ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (j : Z ⟶ S) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))
  (ρ : T ⟶ Z) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Effective klt normalization restricts to an actual open scheme and gives
roundup section comparison on any further proper crepant model, without a
supplied SNC family on the open restriction. -/
theorem normalized_roundup_open_refinement_mem_sections_iff
    (hnormS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s))
    (hcovS : CodimOneChartCovered n K S)
    (cS : EtaleChart K S n) (fS : S.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor S)
    (heff : LogPairBoundaryEffective cS fS d (D + d • E₀))
    (hklt : LogPairIsKlt cS fS d (D + d • E₀))
    (cZ : EtaleChart K Z n) (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (ρ ≫ j)
        (dominantFunctionFieldAlgHom_comp_bijective j ρ hj hρ) cS fS d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (U : Z.Opens) [Nonempty U] (z : Z.functionField) :
    letI := dominant_preimage_nonempty ρ U
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom z) ∈ E₁.sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := Z) U).symm z ∈ (cartierPullback j E₀).sections U := by
  have hnormZ : ∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z) := by
    intro z
    letI := hnormS (j z)
    exact IsIntegrallyClosed.of_equiv
      (RingEquiv.ofBijective (j.stalkMap z).hom (ConcreteCategory.bijective_of_isIso _))
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcovZ := codimOneChartCovered_open_immersion j hcovS
  have hEffZ := logPairBoundaryEffective_open_crepant_pullback j hj hnormS hcovS
    cS fS d (D + d • E₀) heff cZ
  have hKltZ := logPairIsKlt_crepant_pullback_without_properness j hj
    cS fS d hd (D + d • E₀) hklt cZ
  rw [cartierPullback_add, cartierPullback_nsmul] at hEffZ hKltZ
  have hE₁' : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ cZ
        (crepantPullbackFormUnit j hj cS fS cZ) d (cartierPullback j D)
        cT etaleCharts_cover) (t : T) : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hE₁ t, crepantBoundaryCartier_comp j ρ hj hρ]
  exact crepant_roundup_mem_sections_iff_on_open ρ hρ hnormZ hnormT hcovZ cZ
    (crepantPullbackFormUnit j hj cS fS cZ) d hd (cartierPullback j D) (cartierPullback j E₀)
    hEffZ hKltZ cT E₁ hE₁' U z

end OpenRefinement

section SNCOpenRefinement

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X S Z T : Scheme.{u}}
  [IsIntegral X] [IsIntegral S] [IsIntegral Z] [IsIntegral T]
  [IsNoetherian S] [IsLocallyNoetherian Z] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [S.Over (Spec (CommRingCat.of K))]
  [Z.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (S ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  [IsSeparated (S ↘ Spec (CommRingCat.of K))]
  (π : S ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (j : Z ⟶ S) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]
  (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))
  (ρ : T ⟶ Z) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The fixed actual SNC roundup compares with an actual locally constructed
proper crepant model. Normalization and its open restriction are internal. -/
theorem snc_roundup_open_refinement_mem_sections_iff
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cS : EtaleChart K S n) (cZ : EtaleChart K Z n)
    (cT : EtaleChart K T n) {r : ℕ} (ξ : Fin r → S) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ s : CodimensionOnePoint S, (s : S) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover) (s : S) = 0)
    (E₀ : CartierDivisor S) (heff : E₀.IsEffective)
    (hE₀ : ∀ s : CodimensionOnePoint S, cartierCoefficient E₀ (s : S) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover)
        (s : S) : ℝ) / (d : ℝ))⌉)
    (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ((ρ ≫ j) ≫ π)
        (dominantFunctionFieldAlgHom_comp_bijective π (ρ ≫ j) hπ
          (dominantFunctionFieldAlgHom_comp_bijective j ρ hj hρ)) c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (U : Z.Opens) [Nonempty U] (z : Z.functionField) :
    letI := dominant_preimage_nonempty ρ U
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom z) ∈ E₁.sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := Z) U).symm z ∈ (cartierPullback j E₀).sections U := by
  letI : Smooth (S ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s) :=
    fun s => smooth_stalk_isIntegrallyClosed (K := K) s
  have hcovS : CodimOneChartCovered n K S := by
    intro s _
    exact Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S) (n := n)).symm ▸ Opens.mem_top s)
  haveI : QuasiCompact (S ↘ Spec (CommRingCat.of K)) := quasiCompact_of_noetherianSpace_source _
  obtain ⟨hEffN, hKltN⟩ := crepant_source_roundup_normalized_pair_effective_klt
    π hπ hnormS c f d hd D cS ξ hinj hξ hsnc hsupport E₀ heff hE₀
  have hE₁' : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (ρ ≫ j)
        (dominantFunctionFieldAlgHom_comp_bijective j ρ hj hρ) cS
        (crepantPullbackFormUnit π hπ c f cS) d (cartierPullback π D)
        cT etaleCharts_cover) (t : T) : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hE₁ t, crepantBoundaryCartier_comp π (ρ ≫ j) hπ
      (dominantFunctionFieldAlgHom_comp_bijective j ρ hj hρ)]
  exact normalized_roundup_open_refinement_mem_sections_iff j hj ρ hρ hnormS hcovS cS
    (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) E₀ hEffN hKltN
    cZ cT E₁ hE₁' U z

end SNCOpenRefinement

section Nearby

variable {K : Type u} [Field K] {n : ℕ} {X T B : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The actual nearby base-section lattice is unchanged by the normalized
proper crepant refinement, for every prescribed base point and rational function. -/
theorem normalized_roundup_nearby_base_section_lattice_iff
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d (D + d • E₀))
    (hklt : LogPairIsKlt c f d (D + d • E₀))
    (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (g : X ⟶ B) [IsIntegral B] [IsDominant g] (η : B) (z : X.functionField) :
    (∃ (U : B.Opens) (hηU : η ∈ U),
      letI : Nonempty U := ⟨⟨η, hηU⟩⟩
      letI := dominant_preimage_nonempty (ρ ≫ g) U
      (rationalFunctionsEquiv (X := T) ((ρ ≫ g) ⁻¹ᵁ U)).symm
        ((dominantFunctionFieldMap ρ).hom z) ∈ E₁.sections ((ρ ≫ g) ⁻¹ᵁ U)) ↔
    (∃ (U : B.Opens) (hηU : η ∈ U),
      letI : Nonempty U := ⟨⟨η, hηU⟩⟩
      letI := dominant_preimage_nonempty g U
      (rationalFunctionsEquiv (X := X) (g ⁻¹ᵁ U)).symm z ∈ E₀.sections (g ⁻¹ᵁ U)) := by
  constructor
  · rintro ⟨U, hηU, hs⟩
    letI : Nonempty U := ⟨⟨η, hηU⟩⟩
    letI := dominant_preimage_nonempty (ρ ≫ g) U
    letI := dominant_preimage_nonempty g U
    refine ⟨U, hηU, ?_⟩
    apply (crepant_roundup_mem_sections_iff_on_open ρ hρ hnormX hnormT hcov c f d hd D E₀
      heff hklt cT E₁ hE₁ (g ⁻¹ᵁ U) z).mp
    simpa only [Scheme.Hom.comp_preimage] using hs
  · rintro ⟨U, hηU, hs⟩
    letI : Nonempty U := ⟨⟨η, hηU⟩⟩
    letI := dominant_preimage_nonempty g U
    letI := dominant_preimage_nonempty (ρ ≫ g) U
    refine ⟨U, hηU, ?_⟩
    have h := (crepant_roundup_mem_sections_iff_on_open ρ hρ hnormX hnormT hcov c f d hd D E₀
      heff hklt cT E₁ hE₁ (g ⁻¹ᵁ U) z).mpr hs
    simpa only [Scheme.Hom.comp_preimage] using h

/-- Arbitrary Cartier twists use the same effective exceptional difference,
so their actual rational lattices compare without a new normalized-pair input. -/
theorem normalized_roundup_cartier_twisted_mem_sections_iff
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D E₀ : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d (D + d • E₀))
    (hklt : LogPairIsKlt c f d (D + d • E₀))
    (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (A : CartierDivisor X) (U : X.Opens) [Nonempty U] (z : X.functionField) :
    letI := dominant_preimage_nonempty ρ U
    (rationalFunctionsEquiv (X := T) (ρ ⁻¹ᵁ U)).symm
      ((dominantFunctionFieldMap ρ).hom z) ∈
        (E₁ + cartierPullback ρ A).sections (ρ ⁻¹ᵁ U) ↔
      (rationalFunctionsEquiv (X := X) U).symm z ∈ (E₀ + A).sections U := by
  letI := dominant_preimage_nonempty ρ U
  obtain ⟨hC, hEx, -⟩ := crepant_roundup_difference_effective_exceptional_unit_iso
    ρ hρ hnormX hnormT hcov c f d hd D E₀ heff hklt cT E₁ hE₁
  have h := mem_sections_effective_exceptional_cartierPullback_iff_on_open
    hnormX hnormT ρ hρ (E₁ - cartierPullback ρ E₀) hC hEx (E₀ + A) U z
  have heq : cartierPullback ρ (E₀ + A) + (E₁ - cartierPullback ρ E₀) =
      E₁ + cartierPullback ρ A := by
    rw [cartierPullback_add]
    abel
  simpa only [heq] using h

end Nearby

end MixedFujita
