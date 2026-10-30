/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RoundupRefinementBaseLattice
public import MixedFujita.LocalCanonicalBasePrimeRationalSectionLattice

/-!
Express the canonical local base-prime lattice on the same fixed actual
SNC roundup. The normalized reference and higher local resolution are
constructed internally and eliminated from the conclusion. The returned
sections use the actual open pullback of the original fixed Cartier divisor.
-/

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

/-- On the same fixed SNC roundup, construct every local base-prime
Cartier/rational section lattice with the original canonical discriminant
coefficient. No local reference divisor or resolution is supplied or returned. -/
theorem exists_fixed_snc_roundup_canonical_base_prime_lattice
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
    (W : B.Opens) (hηW : (η : B) ∈ W) :
    ∃ (U : B.affineOpens) (_ : U.1 ≤ W) (hηU : (η : B) ∈ U.1),
      letI : Nonempty U.1 := ⟨⟨(η : B), hηU⟩⟩
      letI : Nonempty (q ⁻¹ᵁ U.1) := dominant_preimage_nonempty q U.1
      letI : (q ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
        ⟨(q ⁻¹ᵁ U.1).ι ≫ (S ↘ Spec (CommRingCat.of K))⟩
      letI : (q ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      letI : IsDominant (q ⁻¹ᵁ U.1).ι :=
        ⟨(q ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
      letI : IsDominant (q ∣_ U.1) := isDominant_morphismRestrict_integral q U.1
      (∀ L : CartierDivisor U.1.toScheme,
        (∃ V : U.1.toScheme.Opens, (⟨(η : B), hηU⟩ : U.1.toScheme) ∈ V ∧
          Scheme.Modules.Hom.app (Scheme.toRationalFunctions (q ⁻¹ᵁ U.1).toScheme)
            ((q ∣_ U.1) ⁻¹ᵁ V) (1 : Γ((q ⁻¹ᵁ U.1).toScheme, (q ∣_ U.1) ⁻¹ᵁ V)) ∈
              (cartierPullback (q ⁻¹ᵁ U.1).ι E₀ + cartierPullback (q ∣_ U.1) L).sections
                ((q ∣_ U.1) ⁻¹ᵁ V)) ↔
          0 ≤ cartierCoefficient L (⟨(η : B), hηU⟩ : U.1.toScheme) +
            ⌈-(subKltBasePrimeDiscriminantCoefficients q hnormB cS
              (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) hkltS η)⌉) ∧
      ∀ u : U.1.toScheme.functionFieldˣ,
        (∃ V : U.1.toScheme.Opens, (⟨(η : B), hηU⟩ : U.1.toScheme) ∈ V ∧
          Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul (q ⁻¹ᵁ U.1).toScheme
            ((dominantFunctionFieldMap (q ∣_ U.1)).hom (u : U.1.toScheme.functionField)))
            ((q ∣_ U.1) ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app (Scheme.toRationalFunctions (q ⁻¹ᵁ U.1).toScheme)
              ((q ∣_ U.1) ⁻¹ᵁ V) (1 : Γ((q ⁻¹ᵁ U.1).toScheme, (q ∣_ U.1) ⁻¹ᵁ V))) ∈
                (cartierPullback (q ⁻¹ᵁ U.1).ι E₀).sections ((q ∣_ U.1) ⁻¹ᵁ V)) ↔
          0 ≤ U.1.toScheme.ord (u : U.1.toScheme.functionField)
            (⟨(η : B), hηU⟩ : U.1.toScheme) +
            ⌈-(subKltBasePrimeDiscriminantCoefficients q hnormB cS
              (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) hkltS η)⌉ := by
  let fS := crepantPullbackFormUnit π hπ c f cS
  let DS := cartierPullback π D
  letI : Smooth (S ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s) :=
    fun s => smooth_stalk_isIntegrallyClosed (K := K) s
  have hcovS : CodimOneChartCovered n K S := by
    intro s _
    exact Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S) (n := n)).symm ▸ Opens.mem_top s)
  obtain ⟨hEffN, hKltN⟩ := crepant_source_roundup_normalized_pair_effective_klt
    π hπ hnormS c f d hd D cS ξ hinj hξ hsnc hsupport E₀ heff hE₀
  obtain ⟨U, hUW, hηU, hdata⟩ :=
    exists_local_snc_roundup_canonical_cartier_and_rational_lattice q hnormB η
      cS fS d hd DS hkltS W hηW
  refine ⟨U, hUW, hηU, ?_⟩
  letI : Nonempty U.1 := ⟨⟨(η : B), hηU⟩⟩
  letI : Nonempty (q ⁻¹ᵁ U.1) := dominant_preimage_nonempty q U.1
  letI : (q ⁻¹ᵁ U.1).toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨(q ⁻¹ᵁ U.1).ι ≫ (S ↘ Spec (CommRingCat.of K))⟩
  letI : (q ⁻¹ᵁ U.1).ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  letI : IsDominant (q ⁻¹ᵁ U.1).ι :=
    ⟨(q ⁻¹ᵁ U.1).ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  letI : IsDominant (q ∣_ U.1) := isDominant_morphismRestrict_integral q U.1
  obtain ⟨cV, hlocal⟩ := hdata
  dsimp only at hlocal
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, E₁, -, hE₁, hLs, hUs⟩ := hlocal
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  let j := (q ⁻¹ᵁ U.1).ι
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion j
  let fV := crepantPullbackFormUnit j hj cS fS cV
  let DV := cartierPullback j DS
  let EV := cartierPullback j E₀
  have hnormV : ∀ v : (q ⁻¹ᵁ U.1).toScheme,
      IsIntegrallyClosed ((q ⁻¹ᵁ U.1).toScheme.presheaf.stalk v) := by
    intro v
    letI := hnormS (j v)
    exact IsIntegrallyClosed.of_equiv
      (RingEquiv.ofBijective (j.stalkMap v).hom (ConcreteCategory.bijective_of_isIso _))
  have hcovV := codimOneChartCovered_open_immersion j hcovS
  have hEffV := logPairBoundaryEffective_open_crepant_pullback j hj hnormS hcovS
    cS fS d (DS + d • E₀) hEffN cV
  have hKltV := logPairIsKlt_crepant_pullback_without_properness j hj
    cS fS d hd (DS + d • E₀) hKltN cV
  rw [cartierPullback_add, cartierPullback_nsmul] at hEffV hKltV
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  refine ⟨?_, ?_⟩
  · intro L
    exact (normalized_roundup_base_neighborhood_unit_lattice_iff ρ hρ hnormV hnormT hcovV
      cV fV d hd DV EV hEffV hKltV cT E₁ hE₁ (q ∣_ U.1) (⟨(η : B), hηU⟩ : U.1.toScheme) L).symm.trans
        (hLs L)
  · intro u
    exact (normalized_roundup_base_neighborhood_rational_lattice_iff ρ hρ hnormV hnormT hcovV
      cV fV d hd DV EV hEffV hKltV cT E₁ hE₁ (q ∣_ U.1) (⟨(η : B), hηU⟩ : U.1.toScheme) u).symm.trans
        (hUs u)

end MixedFujita
