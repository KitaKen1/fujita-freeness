/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalBasePrimeRationalSectionLattice
public import MixedFujita.CanonicalSubKltBasePrimeLocalTests
public import MixedFujita.NormalBasePrimeUniformizer
public import MixedFujita.KltNonproperBirationalTests

/-!
At every original normal base prime and inside any prescribed base open,
construct the normalized equation, crepant restricted pair, actual joint SNC
source and effective roundup internally. All local base Cartier twists and
nonzero rational base functions have the exact original canonical discriminant
lattice. The original local tests are used directly, so no comparison with a
newly chosen canonical threshold on the restricted base is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
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
  (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
  (η : CodimensionOnePoint Y)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D : CartierDivisor X) (hklt : LogPairIsKlt c f d D)
  (W : Y.Opens) (hηW : (η : Y) ∈ W)

include hηW

/-- Every original base prime has an internally constructed actual local
Cartier/rational section lattice, inside any prescribed neighbourhood, with
no supplied normalized divisor or SNC model and with the original canonical
sub-klt discriminant coefficient retained. -/
theorem exists_local_snc_roundup_canonical_cartier_and_rational_lattice :
    ∃ (U : Y.affineOpens) (_ : U.1 ≤ W) (hηU : (η : Y) ∈ U.1),
      letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
      letI : Nonempty (g ⁻¹ᵁ U.1) := dominant_preimage_nonempty g U.1
      letI : (g ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
        ⟨(g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
      letI : (g ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      letI : IsDominant (g ⁻¹ᵁ U.1).ι :=
        ⟨(g ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
      letI : IsDominant (g ∣_ U.1) := isDominant_morphismRestrict_integral g U.1
      ∃ cU : EtaleChart K (g ⁻¹ᵁ U.1).toScheme n,
        let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U.1).ι
          (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U.1).ι) c f cU
        let DU := cartierPullback (g ⁻¹ᵁ U.1).ι D
        ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
          (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
          (ρ : T ⟶ (g ⁻¹ᵁ U.1).toScheme) (_ : IsDominant ρ)
          (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
          (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
          (cT : EtaleChart K T n) (E : CartierDivisor T),
          E.IsEffective ∧
          (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
            ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ cU fU d DU cT etaleCharts_cover)
              (t : T) : ℝ) / (d : ℝ))⌉) ∧
          (∀ L : CartierDivisor U.1.toScheme,
            (∃ V : U.1.toScheme.Opens, (⟨(η : Y), hηU⟩ : U.1.toScheme) ∈ V ∧
              Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
                (1 : Γ(T, (ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)) ∈
                  (E + cartierPullback (ρ ≫ (g ∣_ U.1)) L).sections
                    ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)) ↔
              0 ≤ cartierCoefficient L (⟨(η : Y), hηU⟩ : U.1.toScheme) +
                ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉) ∧
          ∀ u : U.1.toScheme.functionFieldˣ,
            (∃ V : U.1.toScheme.Opens, (⟨(η : Y), hηU⟩ : U.1.toScheme) ∈ V ∧
              Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
                ((dominantFunctionFieldMap (ρ ≫ (g ∣_ U.1))).hom
                  (u : U.1.toScheme.functionField))) ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
                (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T)
                  ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
                  (1 : Γ(T, (ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V))) ∈
                    E.sections ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)) ↔
              0 ≤ U.1.toScheme.ord (u : U.1.toScheme.functionField)
                (⟨(η : Y), hηU⟩ : U.1.toScheme) +
                ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉ := by
  letI := hnormY (η : Y)
  obtain ⟨U, hUW, hηU, H, hH, hHη⟩ := normal_base_prime_effective_cartier_neighborhood η W hηW
  refine ⟨U, hUW, hηU, ?_⟩
  letI : Nonempty U.1 := ⟨⟨(η : Y), hηU⟩⟩
  letI : Nonempty (g ⁻¹ᵁ U.1) := dominant_preimage_nonempty g U.1
  letI : (g ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  letI : (g ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (g ⁻¹ᵁ U.1).ι :=
    ⟨(g ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (g ∣_ U.1) := isDominant_morphismRestrict_integral g U.1
  haveI : LocallyOfFiniteType ((g ⁻¹ᵁ U.1).toScheme ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFiniteType ((g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  haveI : IsSeparated ((g ⁻¹ᵁ U.1).toScheme ↘ Spec (CommRingCat.of K)) := by
    change IsSeparated ((g ⁻¹ᵁ U.1).ι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  letI : NoetherianSpace (g ⁻¹ᵁ U.1).toScheme :=
    (g ⁻¹ᵁ U.1).ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  haveI : QuasiCompact ((g ⁻¹ᵁ U.1).toScheme ↘ Spec (CommRingCat.of K)) :=
    quasiCompact_of_noetherianSpace_source _
  obtain ⟨cU⟩ := exists_etaleChart_on_integral_open_immersion (g ⁻¹ᵁ U.1).ι c
  refine ⟨cU, ?_⟩
  let fU := crepantPullbackFormUnit (g ⁻¹ᵁ U.1).ι
    (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U.1).ι) c f cU
  let DU := cartierPullback (g ⁻¹ᵁ U.1).ι D
  let θ : U.1.toScheme := ⟨(η : Y), hηU⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective U.1.ι θ
      (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap θ))).trans η.property
  let ηU : CodimensionOnePoint U.1.toScheme := ⟨θ, hθ⟩
  let e : Y.presheaf.stalk (η : Y) ≃+* U.1.toScheme.presheaf.stalk θ :=
    RingEquiv.ofBijective (U.1.ι.stalkMap θ).hom
      (ConcreteCategory.bijective_of_isIso (U.1.ι.stalkMap θ))
  letI : IsIntegrallyClosed (U.1.toScheme.presheaf.stalk θ) := IsIntegrallyClosed.of_equiv e
  have hkltU : LogPairIsKlt cU fU d DU :=
    logPairIsKlt_crepant_pullback_without_properness (g ⁻¹ᵁ U.1).ι
      (dominantFunctionFieldMap_bijective_of_isOpenImmersion (g ⁻¹ᵁ U.1).ι)
      c f d hd D hklt cU
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp, hHsupp⟩ :=
    exists_proper_snc_model_with cU fU d DU
      (fun _ : PUnit.{1} => cartierPullback (g ∣_ U.1) H)
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  haveI : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  haveI : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨E, heff, hE⟩ := exists_effective_snc_boundary_roundup
    (crepantBoundaryCartier ρ hρ cU fU d DU cT etaleCharts_cover) d hd ξ hinj hcoh hsnc hsupp
    (fun i => logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ cU fU d DU hkltU cT ⟨ξ i, hcoh i⟩)
  let b : ℤ := ⌈-(subKltBasePrimeDiscriminantCoefficients g hnormY c f d hd D hklt η)⌉
  have hcut (p : ℕ) :
      (∀ t : CodimensionOnePoint T, θ ∈ closure ({(ρ ≫ (g ∣_ U.1)) (t : T)} : Set U.1.toScheme) →
        0 ≤ cartierCoefficient (E - p • cartierPullback (ρ ≫ (g ∣_ U.1)) H) (t : T)) ↔
        (p : ℤ) ≤ b := by
    have hlocal := snc_roundup_integer_coefficients_overBasePoint_iff_klt ρ hρ (g ∣_ U.1) θ
      cU fU d hd DU (cartierPullback (g ∣_ U.1) H) cT ξ hinj hcoh hsnc hsupp
      (hHsupp PUnit.unit) E hE p
    have htest : LogPairIsKltOverBasePoint (g ∣_ U.1) θ cU fU d
        (DU + (d * p) • cartierPullback (g ∣_ U.1) H) ↔
        (p : ℚ) < canonicalSubKltBasePrimeThreshold g η c f d hd D hklt := by
      simpa only [one_mul, one_nsmul, Nat.cast_one, div_one] using
        (canonicalSubKltBasePrimeThreshold_local_tests g η c f d hd D hklt
          U.1 hηU H hH hHη cU p 1 (by omega)).1
    have h := (hlocal.trans htest).trans
      (integer_lt_threshold_iff_le_discriminant_roundup (p : ℤ)
        (canonicalSubKltBasePrimeThreshold g η c f d hd D hklt))
    simpa only [cartierPullback_comp, b, subKltBasePrimeDiscriminantCoefficients] using h
  have hL := base_prime_cartier_neighborhood_lattice_of_integer_cutoff hnormT
    (ρ ≫ (g ∣_ U.1)) ηU H hH hHη E heff b hcut
  refine ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, E, heff, hE, hL, ?_⟩
  intro u
  let v : T.functionFieldˣ :=
    Units.map (dominantFunctionFieldMap (ρ ≫ (g ∣_ U.1))).hom.toMonoidHom u
  have hmem (V : U.1.toScheme.Opens) :
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
        ((dominantFunctionFieldMap (ρ ≫ (g ∣_ U.1))).hom (u : U.1.toScheme.functionField)))
        ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
          (1 : Γ(T, (ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V))) ∈ E.sections ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V) ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)
        (1 : Γ(T, (ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V)) ∈
          (E + cartierPullback (ρ ≫ (g ∣_ U.1)) (principalCartierDivisor U.1.toScheme u)).sections
            ((ρ ≫ (g ∣_ U.1)) ⁻¹ᵁ V) := by
    rw [cartierPullback_principal]
    exact cartier_rational_unit_mem_sections_iff_unit_of_add_principal E v _
  have hprincipal := hL (principalCartierDivisor U.1.toScheme u)
  rw [cartierCoefficient_principal] at hprincipal
  refine Iff.trans ?_ hprincipal
  exact exists_congr (fun V : U.1.toScheme.Opens => and_congr_right (fun _ => hmem V))

end MixedFujita
