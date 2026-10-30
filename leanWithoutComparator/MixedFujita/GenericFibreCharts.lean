/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreTransversality
public import MixedFujita.FibreChart
public import MixedFujita.NonproperGenericSmoothness
public import MixedFujita.EtaleChartStrataBertini
public import MixedFujita.AffineEtaleChartModel
public import MixedFujita.SmoothLemmaThreeRealization
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
Generic fibre charts (step 9, generic restriction). Let T be smooth of dimension n + d over a
field of characteristic zero with a simple normal crossing family, and B → Γ(T) a map from a
finitely generated domain (a morphism T → Spec B). There is h ≠ 0 in B such that at every point
t₀ of T over the open D(h) and for every system u of étale coordinates of B near the image of t₀,
some simple normal crossing chart at t₀ has the pullbacks of the u_l as its last d coordinates
and all its members among the first n coordinates (`exists_generic_fibreCharts`).

Finitely many simple normal crossing charts cover T. On each chart every coordinate stratum
{x_a = 0 : a ∈ S} is smooth over K, hence regular, so by generic smoothness without properness
it is smooth over a nonempty open of Spec B (`exists_generic_formallySmooth_stratum`); h is the
product of the finitely many equations of these opens. Over D(h) the local ring of the stratum of
the members through t₀ is formally smooth over B, so the differentials of the member coordinates
and of the u_l are independent on its residue field (`linearIndependent_kaehler_of_formallySmooth_quotient`),
and the fibre chart follows (`exists_fibreChart`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

section Stratum

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseOpenAlgebra

/-- Generic smoothness of a coordinate stratum of an étale chart over a finitely generated domain:
the local rings of the stratum over a nonempty basic open of the base are formally smooth. -/
theorem exists_generic_formallySmooth_stratum [CharZero K]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {N : ℕ} (c : EtaleChart K T N)
    (S : Set (Fin N)) (B : Type u) [CommRing B] [IsDomain B] [Algebra K B]
    [Algebra.FiniteType K B] (φ : B →ₐ[K] Γ(T, c.U)) :
    ∃ h : B, h ≠ 0 ∧ ∀ (p : Ideal (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)) [p.IsPrime],
      h ∉ p.comap ((Ideal.Quotient.mk (etaleChartStratumIdeal c S)).comp φ.toRingHom) →
      ((algebraMap (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S) (Localization.AtPrime p)).comp
        ((Ideal.Quotient.mk (etaleChartStratumIdeal c S)).comp φ.toRingHom)).FormallySmooth := by
  classical
  have hsm : Algebra.Smooth K (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S) :=
    etaleChart_stratum_smooth c S
  set f : B →+* Γ(T, c.U) ⧸ etaleChartStratumIdeal c S :=
    (Ideal.Quotient.mk (etaleChartStratumIdeal c S)).comp φ.toRingHom with hf
  have hfK : f.comp (algebraMap K B) =
      algebraMap K (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S) := by
    ext k
    simp only [hf, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes]
    rfl
  have hft : f.FiniteType := by
    have h1 : (algebraMap K (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)).FiniteType :=
      RingHom.finiteType_algebraMap.mpr inferInstance
    rw [← hfK] at h1
    exact RingHom.FiniteType.of_comp_finiteType h1
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : IsNoetherianRing (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S) :=
    Algebra.FiniteType.isNoetherianRing K _
  have hfp : f.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp hft
  let g : Spec (CommRingCat.of (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)) ⟶
      Spec (CommRingCat.of B) := Spec.map (CommRingCat.ofHom f)
  have : LocallyOfFinitePresentation g := HasRingHomProperty.Spec_iff.mpr hfp
  have hreg : ∀ t : Spec (CommRingCat.of (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)),
      (Spec (CommRingCat.of (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S))).IsRegularAt t := by
    intro t
    have : Smooth (Spec.map (CommRingCat.ofHom
        (algebraMap K (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr hsm)
    have : ∀ y : Spec (CommRingCat.of K),
        IsRegularLocalRing ((Spec (CommRingCat.of K)).presheaf.stalk y) := fun y => inferInstance
    exact isRegularLocalRing_stalk_of_smooth
      (Spec.map (CommRingCat.ofHom (algebraMap K (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)))) t
  letI : (Spec (CommRingCat.of B)).Over (Spec (CommRingCat.of K)) := specAlgebraOver (K := K) B
  obtain ⟨V, hηV, hV⟩ := exists_open_genericPoint_smooth_of_regular K g hreg
  rw [genericPoint_eq_bot_of_affine] at hηV
  obtain ⟨_, ⟨h, rfl⟩, hηh, hhV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hηV V.isOpen
  refine ⟨h, fun h0 => ?_, fun p _ hp => ?_⟩
  · have hηh' : (⊥ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen h := hηh
    rw [PrimeSpectrum.mem_basicOpen, h0] at hηh'
    exact hηh' (Ideal.zero_mem _)
  · let p' : Spec (CommRingCat.of (Γ(T, c.U) ⧸ etaleChartStratumIdeal c S)) := ⟨p, inferInstance⟩
    have hgp : g p' ∈ V := hhV (show g p' ∈ PrimeSpectrum.basicOpen h from hp)
    have hsmooth := hV p' hgp
    rw [Scheme.Hom.mem_smoothLocus] at hsmooth
    have h2 := (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom f) p')).mp hsmooth
    have h1 : (algebraMap B (Localization.AtPrime
        (PrimeSpectrum.comap (CommRingCat.ofHom f).hom p').asIdeal)).FormallySmooth :=
      RingHom.formallySmooth_algebraMap.mpr (Algebra.FormallySmooth.of_isLocalization
        (Rₘ := Localization.AtPrime
          (PrimeSpectrum.comap (CommRingCat.ofHom f).hom p').asIdeal)
        (PrimeSpectrum.comap (CommRingCat.ofHom f).hom p').asIdeal.primeCompl)
    have h3 := h1.comp h2
    simp only [CommRingCat.hom_ofHom] at h3
    convert h3 using 1
    ext b
    exact (Localization.localRingHom_to_map (PrimeSpectrum.comap f p').asIdeal p f rfl b).symm

end Stratum

section Main

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra

omit [T.Over (Spec (CommRingCat.of K))] in
/-- The base field acts on the sections over an open through the restriction of the global
sections. -/
theorem baseRing_restrict [T.Over (Spec (CommRingCat.of K))] (U : T.Opens) (k : K) :
    T.presheaf.map (homOfLE le_top).op (Scheme.Modules.baseRingToGlobalSections K T k) =
      algebraMap K Γ(T, U) k := by
  change _ = ((T.baseRingToStructurePresheaf K).app (op U)).hom k
  rw [Scheme.baseRingToStructurePresheaf_app]
  rfl

/-- The restriction of a map from B to the global sections, as a map of K-algebras to the
sections over an open. -/
noncomputable def globalRingHomRestrict {B : Type u} [CommRing B] [Algebra K B]
    (φ : B →+* Γ(T, ⊤))
    (hφ : ∀ k : K, φ (algebraMap K B k) = Scheme.Modules.baseRingToGlobalSections K T k)
    (U : T.Opens) : B →ₐ[K] Γ(T, U) where
  toRingHom := (T.presheaf.map (homOfLE le_top).op).hom.comp φ
  commutes' k := by
    change (T.presheaf.map (homOfLE le_top).op).hom (φ (algebraMap K B k)) =
      ((T.baseRingToStructurePresheaf K).app (op U)).hom k
    rw [hφ, Scheme.baseRingToStructurePresheaf_app]
    rfl

theorem globalRingHomRestrict_apply {B : Type u} [CommRing B] [Algebra K B]
    (φ : B →+* Γ(T, ⊤))
    (hφ : ∀ k : K, φ (algebraMap K B k) = Scheme.Modules.baseRingToGlobalSections K T k)
    (U : T.Opens) (b : B) :
    globalRingHomRestrict φ hφ U b = T.presheaf.map (homOfLE le_top).op (φ b) := rfl

/-- Generic fibre charts: over a nonempty basic open of the base, every point has a simple normal
crossing chart whose last coordinates are the pullbacks of given étale coordinates of the base. -/
theorem exists_generic_fibreCharts [CharZero K] {n d r : ℕ}
    [SmoothOfRelativeDimension (n + d) (T ↘ Spec (CommRingCat.of K))] [CompactSpace T]
    (ξ : Fin r → T) (hsnc : IsSNCFamily K (n + d) ξ)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    (φ : B →+* Γ(T, ⊤))
    (hφ : ∀ k : K, φ (algebraMap K B k) = Scheme.Modules.baseRingToGlobalSections K T k) :
    ∃ h : B, h ≠ 0 ∧ ∀ t₀ : T, IsUnit (T.presheaf.germ ⊤ t₀ trivial (φ h)) →
      ∀ (u : Fin d → B) (b : B), IsUnit (T.presheaf.germ ⊤ t₀ trivial (φ b)) →
        (MvPolynomial.aeval (R := K)
          (fun l => algebraMap B (Localization.Away b) (u l))).toRingHom.FormallyEtale →
        ∃ (Fc : EtaleChart K T (n + d)) (hFc : t₀ ∈ Fc.U) (σF : Fin r → Option (Fin (n + d))),
          IsSNCChart Fc ξ σF ∧ (∀ k a, σF k = some a → (a : ℕ) < n) ∧
          ∀ l, etaleChartStalkCoords Fc t₀ hFc (MvPolynomial.X (Fin.natAdd n l)) =
            T.presheaf.germ ⊤ t₀ trivial (φ (u l)) := by
  classical
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (n + d) _
  -- a finite cover by simple normal crossing charts
  choose c σ hmem hcsnc using hsnc
  obtain ⟨s, hs⟩ : ∃ s : Finset T, ∀ t : T, ∃ t' ∈ s, t ∈ (c t').U := by
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t => ((c t).U : Set T))
      (fun t => (c t).U.isOpen) (fun t _ => Set.mem_iUnion.mpr ⟨t, hmem t⟩)
    exact ⟨s, fun t => by simpa using hs (Set.mem_univ t)⟩
  -- generic smoothness of all the strata of these charts
  have hstr := fun (t : T) (S : Finset (Fin (n + d))) =>
    exists_generic_formallySmooth_stratum (c t) (↑S) B (globalRingHomRestrict φ hφ (c t).U)
  choose hS hS0 hSsm using hstr
  refine ⟨∏ t ∈ s, ∏ S : Finset (Fin (n + d)), hS t S, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro S _
    exact hS0 t S
  intro t₀ ht₀ u b hb hu
  obtain ⟨t, hts, ht₀c⟩ := hs t₀
  -- the coordinates of the members through t₀
  let S : Finset (Fin (n + d)) :=
    Finset.univ.filter (fun a => ∃ k, σ t k = some a ∧ t₀ ∈ closure ({ξ k} : Set T))
  have hunit : IsUnit (T.presheaf.germ ⊤ t₀ trivial (φ (hS t S))) := by
    refine isUnit_of_dvd_unit (map_dvd _ (map_dvd _ ?_)) ht₀
    exact (Finset.dvd_prod_of_mem _ (Finset.mem_univ S)).trans (Finset.dvd_prod_of_mem _ hts)
  -- the prime of t₀ on the chart and the stratum through t₀
  let 𝔮 : Ideal Γ(T, (c t).U) := ((c t).isAffine.primeIdealOf ⟨t₀, ht₀c⟩).asIdeal
  let I := etaleChartStratumIdeal (c t) (↑S : Set (Fin (n + d)))
  have hI𝔮 : I ≤ 𝔮 := by
    change etaleChartStratumIdeal (c t) (↑S : Set (Fin (n + d))) ≤ 𝔮
    rw [etaleChartStratumIdeal_eq_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, hk, ht₀k⟩ := (Finset.mem_filter.mp ha).2
    have hset := (hcsnc t).2 k
    rw [hk, Option.elim_some] at hset
    have hm : t₀ ∈ closure ({ξ k} : Set T) ∩ (c t).U := ⟨ht₀k, ht₀c⟩
    rw [hset, Scheme.zeroLocus_singleton] at hm
    by_contra hnot
    exact hm.1 ((mem_basicOpen_iff_notMem_primeIdealOf (c t).isAffine t₀ ht₀c _).mpr hnot)
  let p : Ideal (Γ(T, (c t).U) ⧸ I) := 𝔮.map (Ideal.Quotient.mk I)
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔮 := by rwa [Ideal.mk_ker]
  haveI hp : p.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hpcomap : p.comap (Ideal.Quotient.mk I) = 𝔮 :=
    Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective 𝔮 |>.trans
      (sup_eq_left.mpr hker)
  have hhp : hS t S ∉ p.comap ((Ideal.Quotient.mk I).comp
      (globalRingHomRestrict φ hφ (c t).U).toRingHom) := by
    rw [← Ideal.comap_comap, hpcomap]
    intro hmem'
    have h1 : (globalRingHomRestrict φ hφ (c t).U) (hS t S) ∈ 𝔮 := hmem'
    have h2 := (mem_basicOpen_iff_notMem_primeIdealOf (c t).isAffine t₀ ht₀c _).mp
      (show t₀ ∈ T.basicOpen ((globalRingHomRestrict φ hφ (c t).U) (hS t S)) from by
        rw [Scheme.mem_basicOpen _ _ _ ht₀c, globalRingHomRestrict_apply,
          TopCat.Presheaf.germ_res_apply]
        exact hunit)
    exact h2 h1
  have hFS := hSsm t S p hhp
  -- the local rings and the field
  letI : Algebra Γ(T, (c t).U) (T.presheaf.stalk t₀) :=
    TopCat.Presheaf.algebra_section_stalk T.presheaf ⟨t₀, ht₀c⟩
  haveI : IsLocalization.AtPrime (T.presheaf.stalk t₀) 𝔮 :=
    (c t).isAffine.isLocalization_stalk ⟨t₀, ht₀c⟩
  let gC : Γ(T, (c t).U) →+* Localization.AtPrime p :=
    (algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p)).comp (Ideal.Quotient.mk I)
  have hgC : ∀ y : 𝔮.primeCompl, IsUnit (gC y) := by
    intro y
    apply IsLocalization.map_units (Localization.AtPrime p) (⟨Ideal.Quotient.mk I y, ?_⟩ :
      p.primeCompl)
    intro hy
    apply y.2
    have h' : (y : Γ(T, (c t).U)) ∈ p.comap (Ideal.Quotient.mk I) := hy
    rwa [hpcomap] at h'
  let π : T.presheaf.stalk t₀ →+* Localization.AtPrime p :=
    IsLocalization.lift (M := 𝔮.primeCompl) hgC
  have hπ : ∀ γ : Γ(T, (c t).U), π (algebraMap Γ(T, (c t).U) (T.presheaf.stalk t₀) γ) = gC γ :=
    fun γ => IsLocalization.lift_eq hgC γ
  have hgerm : ∀ γ : Γ(T, ⊤), T.presheaf.germ ⊤ t₀ trivial γ =
      algebraMap Γ(T, (c t).U) (T.presheaf.stalk t₀) (T.presheaf.map (homOfLE le_top).op γ) := by
    intro γ
    change _ = T.presheaf.germ (c t).U t₀ ht₀c (T.presheaf.map (homOfLE le_top).op γ)
    rw [TopCat.Presheaf.germ_res_apply]
  letI : Algebra B (T.presheaf.stalk t₀) := ((T.presheaf.germ ⊤ t₀ trivial).hom.comp φ).toAlgebra
  letI : Algebra B (Localization.AtPrime p) :=
    ((algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p)).comp
      ((Ideal.Quotient.mk I).comp (globalRingHomRestrict φ hφ (c t).U).toRingHom)).toAlgebra
  letI : Algebra (T.presheaf.stalk t₀) (Localization.AtPrime p) := π.toAlgebra
  letI : Algebra (T.presheaf.stalk t₀) (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    ((algebraMap (Localization.AtPrime p) (IsLocalRing.ResidueField (Localization.AtPrime p))).comp
      π).toAlgebra
  letI : Algebra B (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    ((algebraMap (Localization.AtPrime p) (IsLocalRing.ResidueField (Localization.AtPrime p))).comp
      (algebraMap B (Localization.AtPrime p))).toAlgebra
  haveI : IsScalarTower B (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower (T.presheaf.stalk t₀) (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower B (T.presheaf.stalk t₀) (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun b' => ?_
    change _ = π (T.presheaf.germ ⊤ t₀ trivial (φ b'))
    rw [hgerm, hπ]
    rfl
  haveI : IsScalarTower K B (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change _ = algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I ((globalRingHomRestrict φ hφ (c t).U) (algebraMap K B k)))
    rw [AlgHom.commutes, ← Ideal.Quotient.mkₐ_eq_mk K, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsScalarTower K (T.presheaf.stalk t₀) (Localization.AtPrime p) := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change _ = π (T.presheaf.germ ⊤ t₀ trivial (Scheme.Modules.baseRingToGlobalSections K T k))
    rw [hgerm, hπ, baseRing_restrict]
    change _ = algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I (algebraMap K Γ(T, (c t).U) k))
    rw [← Ideal.Quotient.mkₐ_eq_mk K, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FormallySmooth B (Localization.AtPrime p) := hFS
  -- the base coordinates are independent on the residue field
  have hbF : IsUnit (algebraMap B (IsLocalRing.ResidueField (Localization.AtPrime p)) b) := by
    have h1 : IsUnit (algebraMap B (T.presheaf.stalk t₀) b) := hb
    have h2 := h1.map π
    change IsUnit (algebraMap (T.presheaf.stalk t₀) (Localization.AtPrime p)
      (algebraMap B (T.presheaf.stalk t₀) b)) at h2
    rw [← IsScalarTower.algebraMap_apply] at h2
    exact h2.map (algebraMap (Localization.AtPrime p)
      (IsLocalRing.ResidueField (Localization.AtPrime p)))
  letI : Algebra (Localization.Away b) (IsLocalRing.ResidueField (Localization.AtPrime p)) :=
    (IsLocalization.Away.lift (S := Localization.Away b) b hbF).toAlgebra
  haveI : IsScalarTower B (Localization.Away b)
      (IsLocalRing.ResidueField (Localization.AtPrime p)) := by
    refine IsScalarTower.of_algebraMap_eq fun b' => ?_
    exact (IsLocalization.Away.lift_eq b hbF b').symm
  have hu' : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime p))
      (fun l => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[B]
        KaehlerDifferential.D K B (u l)) := by
    have h1 : (residueKaehlerMap K (R := B) (O' := Localization.Away b)
        (IsLocalRing.ResidueField (Localization.AtPrime p))) ∘
        (fun l => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[B]
          KaehlerDifferential.D K B (u l)) =
        ⇑((etaleCoordinateBasis _ hu).baseChange
          (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
      funext l
      rw [Function.comp_apply, residueKaehlerMap_tmul, Module.Basis.baseChange_apply,
        etaleCoordinateBasis_apply, MvPolynomial.aeval_X]
    exact LinearIndependent.of_comp _ (h1 ▸ ((etaleCoordinateBasis _ hu).baseChange
      (IsLocalRing.ResidueField (Localization.AtPrime p))).linearIndependent)
  -- the member coordinates are independent on the residue field
  let S' := {a : Fin (n + d) // ∃ k, σ t k = some a ∧ t₀ ∈ closure ({ξ k} : Set T)}
  let z : S' → T.presheaf.stalk t₀ := fun a =>
    etaleChartStalkCoords (c t) t₀ ht₀c (MvPolynomial.X a.1)
  have hz : ∀ a, algebraMap (T.presheaf.stalk t₀) (Localization.AtPrime p) (z a) = 0 := by
    intro a
    change π (algebraMap Γ(T, (c t).U) (T.presheaf.stalk t₀)
      ((c t).coords (MvPolynomial.X a.1))) = 0
    rw [hπ]
    change algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p)
      (Ideal.Quotient.mk I ((c t).coords (MvPolynomial.X a.1))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
    change (c t).coords (MvPolynomial.X a.1) ∈
      etaleChartStratumIdeal (c t) (↑S : Set (Fin (n + d)))
    rw [etaleChartStratumIdeal_eq_span]
    exact Ideal.subset_span ⟨a.1, Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, a.2⟩), rfl⟩
  have hzind : LinearIndependent (IsLocalRing.ResidueField (Localization.AtPrime p))
      (fun a => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[T.presheaf.stalk t₀]
        KaehlerDifferential.D K (T.presheaf.stalk t₀) (z a)) := by
    have h1 : (fun a : S' => (1 : IsLocalRing.ResidueField (Localization.AtPrime p)) ⊗ₜ[
        T.presheaf.stalk t₀] KaehlerDifferential.D K (T.presheaf.stalk t₀) (z a)) =
        ⇑((etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale (c t) t₀
          ht₀c)).baseChange (IsLocalRing.ResidueField (Localization.AtPrime p))) ∘
          Subtype.val := by
      funext a
      rw [Function.comp_apply, Module.Basis.baseChange_apply, etaleCoordinateBasis_apply]
    rw [h1]
    exact ((etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale (c t) t₀
      ht₀c)).baseChange (IsLocalRing.ResidueField (Localization.AtPrime p))).linearIndependent.comp
      _ Subtype.val_injective
  have hind := linearIndependent_kaehler_of_formallySmooth_quotient K (R := B)
    (O := T.presheaf.stalk t₀) (O' := Localization.AtPrime p)
    (F := IsLocalRing.ResidueField (Localization.AtPrime p)) z hz u hu' hzind
  -- the residue field kills the maximal ideal of the stalk
  have hF : ∀ x ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk t₀),
      algebraMap (T.presheaf.stalk t₀) (IsLocalRing.ResidueField (Localization.AtPrime p)) x = 0 := by
    intro x hx
    obtain ⟨⟨γ, y⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
    have hγ : γ ∈ 𝔮 := (IsLocalization.AtPrime.mk'_mem_maximal_iff _ 𝔮 γ y).mp hx
    change IsLocalRing.residue _ (π (IsLocalization.mk' (T.presheaf.stalk t₀) γ y)) = 0
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalization.lift_mk']
    refine Ideal.mul_mem_right _ _ ?_
    change algebraMap (Γ(T, (c t).U) ⧸ I) (Localization.AtPrime p) (Ideal.Quotient.mk I γ) ∈ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ p]
    exact Ideal.mem_map_of_mem _ hγ
  obtain ⟨Fc, hFc, σF, -, hFsnc, hFlt, hFcoord⟩ :=
    exists_fibreChart ξ (σ t) t₀ (c t) ht₀c (hcsnc t)
      (fun l => algebraMap B (T.presheaf.stalk t₀) (u l))
      (IsLocalRing.ResidueField (Localization.AtPrime p)) hF hind
  exact ⟨Fc, hFc, σF, hFsnc, hFlt, hFcoord⟩

end Main

end MixedFujita
