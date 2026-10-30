/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FixedSNCCanonicalBasePrimeLattice
public import MixedFujita.GenericFrameRationalSectionDescent
public import MixedFujita.CartierBaseOpenRationalSections
public import MixedFujita.LocalCanonicalBasePrimeRationalSectionLattice

/-! Unique rational descent and canonical codimension-one pole bounds for
arbitrary sections of the same fixed SNC roundup direct image. No reflexivity
or whole-sheaf representation is inferred from these necessary bounds. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X S B : Scheme.{u}}
  [IsIntegral X] [IsIntegral S] [IsNoetherian S]
  [IsIntegral B] [IsLocallyNoetherian B]
  [X.Over (Spec (CommRingCat.of K))] [S.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (S ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (S ↘ Spec (CommRingCat.of K))]
  [IsSeparated (S ↘ Spec (CommRingCat.of K))]
  (π : S ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [hproperπ : IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (q : S ⟶ B) [IsDominant q] [hproperq : IsProper q]

include hproperπ hproperq

/-- Every nonzero base rational function which is an actual section of
the fixed roundup satisfies the original canonical discriminant pole bound. -/
theorem fixed_snc_roundup_rational_section_canonical_prime_bound

    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (η : CodimensionOnePoint B)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cS : EtaleChart K S n)
    (hkltS : LogPairIsKlt cS (crepantPullbackFormUnit π hπ c f cS) d (cartierPullback π D))
    {r : ℕ} (ξ : Fin r → S) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ s : CodimensionOnePoint S, (s : S) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover) (s : S) = 0)
    (E₀ : CartierDivisor S) (heff : E₀.IsEffective)
    (hE₀ : ∀ s : CodimensionOnePoint S, cartierCoefficient E₀ (s : S) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover)
        (s : S) : ℝ) / (d : ℝ))⌉)
    (W : B.Opens) (hηW : (η : B) ∈ W)
    (z : B.functionField) (hz : z ≠ 0)
    (hs : letI : Nonempty W := ⟨⟨(η : B), hηW⟩⟩
      letI := dominant_preimage_nonempty q W
      (rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ W)).symm
        ((dominantFunctionFieldMap q).hom z) ∈ E₀.sections (q ⁻¹ᵁ W)) :
    0 ≤ B.ord z (η : B) +
      ⌈-(subKltBasePrimeDiscriminantCoefficients q hnormB cS
        (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) hkltS η)⌉ := by
  letI : Nonempty W := ⟨⟨(η : B), hηW⟩⟩
  letI := dominant_preimage_nonempty q W
  obtain ⟨U, hUW, hηU, hdata⟩ := exists_fixed_snc_roundup_canonical_base_prime_lattice
    π hπ q hnormB η c f d hd D cS hkltS ξ hinj hξ hsnc hsupport E₀ heff hE₀ W hηW
  letI : Nonempty U.1 := ⟨⟨(η : B), hηU⟩⟩
  letI : Nonempty (q ⁻¹ᵁ U.1) := dominant_preimage_nonempty q U.1
  letI : (q ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(q ⁻¹ᵁ U.1).ι ≫ (S ↘ Spec (CommRingCat.of K))⟩
  letI : (q ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (q ⁻¹ᵁ U.1).ι :=
    ⟨(q ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant U.1.ι :=
    ⟨U.1.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (q ∣_ U.1) := isDominant_morphismRestrict_integral q U.1
  let u : B.functionFieldˣ := Units.mk0 z hz
  let uU : U.1.toScheme.functionFieldˣ :=
    Units.map (dominantFunctionFieldMap U.1.ι).hom.toMonoidHom u
  have hsU := cartier_rational_section_on_base_open_restriction q E₀ W U.1 hUW z hs
  have hmem : Scheme.Modules.Hom.app
      (Scheme.rationalFunctionsMul (q ⁻¹ᵁ U.1).toScheme
        ((dominantFunctionFieldMap (q ∣_ U.1)).hom (uU : U.1.toScheme.functionField))) ⊤
      (Scheme.Modules.Hom.app (Scheme.toRationalFunctions (q ⁻¹ᵁ U.1).toScheme) ⊤
        (1 : Γ((q ⁻¹ᵁ U.1).toScheme, ⊤))) ∈
      (cartierPullback (q ⁻¹ᵁ U.1).ι E₀).sections ⊤ := by
    have hunit : Scheme.Modules.Hom.app
        (Scheme.rationalFunctionsMul (q ⁻¹ᵁ U.1).toScheme
          ((dominantFunctionFieldMap (q ∣_ U.1)).hom (uU : U.1.toScheme.functionField))) ⊤
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions (q ⁻¹ᵁ U.1).toScheme) ⊤
          (1 : Γ((q ⁻¹ᵁ U.1).toScheme, ⊤))) =
        (rationalFunctionsEquiv (X := (q ⁻¹ᵁ U.1).toScheme) ⊤).symm
          ((dominantFunctionFieldMap (q ∣_ U.1)).hom
            ((dominantFunctionFieldMap U.1.ι).hom z)) := by
      apply (rationalFunctionsEquiv (X := (q ⁻¹ᵁ U.1).toScheme) ⊤).injective
      simp only [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
        Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one,
        LinearEquiv.apply_symm_apply, uU, Units.coe_map, u, Units.val_mk0]
      rfl
    rw [hunit]
    exact hsU
  have hb := (hdata.2 uU).mp ⟨⊤, trivial, by
    simpa only [Scheme.Hom.preimage_top] using hmem⟩
  let θ : U.1.toScheme := ⟨(η : B), hηU⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective U.1.ι θ
      (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap θ))).trans η.property
  let ηU : CodimensionOnePoint U.1.toScheme := ⟨θ, hθ⟩
  letI := hnormB (η : B)
  letI : IsIntegrallyClosed (U.1.toScheme.presheaf.stalk θ) :=
    IsIntegrallyClosed.of_equiv
      (RingEquiv.ofBijective (U.1.ι.stalkMap θ).hom
        (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap θ)))
  letI := normal_codimensionOne_stalk_DVR η
  letI := normal_codimensionOne_stalk_DVR ηU
  have hηeq : U.1.ι (ηU : U.1.toScheme) = (η : B) := by
    simp only [ηU, θ, Scheme.Opens.ι_apply]
  letI : IsDiscreteValuationRing (B.presheaf.stalk (U.1.ι (ηU : U.1.toScheme))) := by
    rw [hηeq]
    infer_instance
  have hηcoh : Order.coheight (U.1.ι (ηU : U.1.toScheme)) = 1 := by
    rw [hηeq]
    exact η.property
  have hord := scheme_ord_pullback_of_stalkMap_bijective U.1.ι ηU hηcoh
    (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap θ)) z
  rw [hηeq] at hord
  change 0 ≤ U.1.toScheme.ord ((dominantFunctionFieldMap U.1.ι).hom z) θ + _ at hb
  rw [hord] at hb
  exact hb

/-- Every actual direct-image section of the fixed SNC roundup descends
uniquely to a rational base function and, when nonzero, obeys all canonical
codimension-one pole bounds on the original base open. -/
theorem fixed_snc_direct_image_section_rational_descent_canonical_prime_bounds

    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cS : EtaleChart K S n)
    (hkltS : LogPairIsKlt cS (crepantPullbackFormUnit π hπ c f cS) d (cartierPullback π D))
    {r : ℕ} (ξ : Fin r → S) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ s : CodimensionOnePoint S, (s : S) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover) (s : S) = 0)
    (E₀ : CartierDivisor S) (heff : E₀.IsEffective)
    (hE₀ : ∀ s : CodimensionOnePoint S, cartierCoefficient E₀ (s : S) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover)
        (s : S) : ℝ) / (d : ℝ))⌉)
    (F : B.Opens) (hgenF : genericPoint B ∈ F)
    [IsIso ((effectiveCartierPushforwardUnitMap q E₀ heff).over F)]
    (W : B.Opens) [Nonempty W] (s : Γ(E₀.sheaf, q ⁻¹ᵁ W)) :
    letI := dominant_preimage_nonempty q W
    ∃! z : B.functionField,
      (dominantFunctionFieldMap q).hom z =
        rationalFunctionsEquiv (X := S) (q ⁻¹ᵁ W)
          (Scheme.Modules.Hom.app E₀.sheafι (q ⁻¹ᵁ W) s) ∧
      ∀ η : CodimensionOnePoint B, (η : B) ∈ W → z = 0 ∨
        0 ≤ B.ord z (η : B) +
          ⌈-(subKltBasePrimeDiscriminantCoefficients q hnormB cS
            (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) hkltS η)⌉ := by
  letI := dominant_preimage_nonempty q W
  obtain ⟨z, hz, huniq⟩ :=
    cartier_direct_image_section_descends_of_generic_unit_frame q E₀ heff F hgenF W s
  refine ⟨z, ⟨hz, ?_⟩, ?_⟩
  · intro η hηW
    by_cases hzero : z = 0
    · exact Or.inl hzero
    · right
      apply fixed_snc_roundup_rational_section_canonical_prime_bound π hπ q hnormB η
        c f d hd D cS hkltS ξ hinj hξ hsnc hsupport E₀ heff hE₀ W hηW z hzero
      rw [hz, LinearEquiv.symm_apply_apply]
      exact E₀.sheafι_app_mem (q ⁻¹ᵁ W) s
  · intro r hr
    exact huniq r hr.1

end MixedFujita
