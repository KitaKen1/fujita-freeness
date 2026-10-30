/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModelThresholdLocality

/-!
Badness along open immersions and localizations (step 9, restriction theorem).

The model form of lct_x ≤ 1/M is local along any open immersion j : U → Y
(`modelThresholdBadAt_openImmersion_iff`): restrict to the open range of j (check-316) and
transport back along the isomorphism of U with it (check-315). For a K-point χ of a localization
A_f of a smooth K-domain A this gives: χ is bad on Spec A_f for the localized family if and only
if its restriction to A is bad on Spec A (`modelThresholdBadAt_away_iff`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

section OpenImmersion

variable {K : Type u} [Field K] {n : ℕ} {U Y : Scheme.{u}} [IsIntegral U] [IsIntegral Y]
  [U.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  (j : U ⟶ Y) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]

/-- Badness is local along open immersions. -/
theorem modelThresholdBadAt_openImmersion_iff (cY : EtaleChart K Y n) (cU : EtaleChart K U n)
    (u : U) {J : Type*} (gY : J → Y.functionField) (gU : J → U.functionField)
    (hg : ∀ i, (dominantFunctionFieldMap j).hom (gY i) = gU i) (M : ℕ) :
    ModelThresholdBadAt cU (1 : U.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cU + principalCartierDivisor U (1 : U.functionFieldˣ))) u gU
      M ↔
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) (j u)
      gY M := by
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion j
  refine ⟨modelThresholdBadAt_of_openImmersion j hj cY cU u gY gU hg M, fun h => ?_⟩
  -- restrict to the open range of j
  let V : Y.Opens := j.opensRange
  have hu : j u ∈ V := ⟨u, rfl⟩
  have : Nonempty V := ⟨⟨j u, hu⟩⟩
  let : V.toScheme.Over (Spec (CommRingCat.of K)) := ⟨V.ι ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  have : V.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  have : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : SmoothOfRelativeDimension n (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + n) (V.ι ≫ (Y ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  obtain ⟨cV⟩ : Nonempty (EtaleChart K V.toScheme n) := by
    obtain ⟨c, -⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := V.toScheme) (n := n)).symm ▸
        Opens.mem_top (⟨j u, hu⟩ : V.toScheme))
    exact ⟨c⟩
  have h1 := modelThresholdBadAt_restrict_opens V cY cV (j u) hu gY
    (fun i => (dominantFunctionFieldMap V.ι).hom (gY i)) (fun i => rfl) M h
  -- and transport back along the isomorphism of the open range with U
  let φ : V.toScheme ⟶ U := j.isoOpensRange.inv
  have hφ : φ ≫ j = V.ι := j.isoOpensRange_inv_comp
  have : IsOpenImmersion φ := inferInstance
  have : IsDominant φ := ⟨φ.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : φ.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change φ ≫ (U ↘ Spec (CommRingCat.of K)) = V.ι ≫ (Y ↘ Spec (CommRingCat.of K))
    rw [← HomIsOver.comp_over (f := j) (S := Spec (CommRingCat.of K)), ← Category.assoc, hφ]
  have hφb : Function.Bijective (dominantFunctionFieldAlgHom (K := K) φ) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion φ
  have hgφ : ∀ i, (dominantFunctionFieldMap φ).hom (gU i) =
      (dominantFunctionFieldMap V.ι).hom (gY i) := by
    intro i
    rw [← hg i]
    change ((dominantFunctionFieldAlgHom (K := K) φ).comp (dominantFunctionFieldAlgHom (K := K) j))
      (gY i) = dominantFunctionFieldAlgHom (K := K) V.ι (gY i)
    rw [← dominantFunctionFieldAlgHom_comp, dominantFunctionFieldAlgHom_congr_hom hφ]
  have hpt : φ ⟨j u, hu⟩ = u := by
    have h2 : j.isoOpensRange.hom u = ⟨j u, hu⟩ := by
      apply V.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, j.isoOpensRange_hom_ι]
      rfl
    rw [← h2]
    change (j.isoOpensRange.hom ≫ j.isoOpensRange.inv) u = u
    rw [Iso.hom_inv_id]
    rfl
  have h3 := modelThresholdBadAt_of_openImmersion φ hφb cU cV ⟨j u, hu⟩ gU
    (fun i => (dominantFunctionFieldMap V.ι).hom (gY i)) hgφ M h1
  rw [hpt] at h3
  exact h3

end OpenImmersion

section Localization

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] specAlgebraOver

/-- The spectrum of a localization A_f of a smooth K-algebra A is smooth of the same relative
dimension. -/
theorem smoothOfRelativeDimension_spec_away {A : Type u} [CommRing A] [Algebra K A]
    [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))] (f : A) :
    SmoothOfRelativeDimension n
      (Spec (CommRingCat.of (Localization.Away f)) ↘ Spec (CommRingCat.of K)) := by
  let j : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))
  have : IsOpenImmersion j := inferInstance
  have hj : j ≫ (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) =
      Spec (CommRingCat.of (Localization.Away f)) ↘ Spec (CommRingCat.of K) := by
    change Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away f)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [← hj]
  have h : SmoothOfRelativeDimension (0 + n) (j ≫ (Spec (CommRingCat.of A) ↘
    Spec (CommRingCat.of K))) := inferInstance
  simpa only [Nat.zero_add] using h

/-- Badness at a K-point of a localization A_f of a smooth K-domain A, for the localized family,
is badness at its restriction to A. -/
theorem modelThresholdBadAt_away_iff {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
    [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))] (f : A)
    [IsDomain (Localization.Away f)]
    [SmoothOfRelativeDimension n
      (Spec (CommRingCat.of (Localization.Away f)) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) n)
    (cXf : EtaleChart K (Spec (CommRingCat.of (Localization.Away f))) n)
    (χ : Localization.Away f →ₐ[K] K) {J : Type*} (g : J → A) (M : ℕ) :
    ModelThresholdBadAt cXf (1 : (Spec (CommRingCat.of (Localization.Away f))).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cXf + principalCartierDivisor
        (Spec (CommRingCat.of (Localization.Away f)))
        (1 : (Spec (CommRingCat.of (Localization.Away f))).functionFieldˣ)))
      (specAlgHomPoint χ)
      (fun j => (Spec (CommRingCat.of (Localization.Away f))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).inv
          (algebraMap A (Localization.Away f) (g j)))) M ↔
    ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
        (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
      (specAlgHomPoint (χ.comp (IsScalarTower.toAlgHom K A (Localization.Away f))))
      (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M := by
  let j : Spec (CommRingCat.of (Localization.Away f)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))
  have : IsOpenImmersion j := inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : j.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away f)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hpt : j (specAlgHomPoint χ) =
      specAlgHomPoint (χ.comp (IsScalarTower.toAlgHom K A (Localization.Away f))) := by
    apply PrimeSpectrum.ext
    ext a
    change algebraMap A (Localization.Away f) a ∈ RingHom.ker χ.toRingHom ↔
      a ∈ RingHom.ker (χ.comp (IsScalarTower.toAlgHom K A (Localization.Away f))).toRingHom
    rw [RingHom.mem_ker, RingHom.mem_ker]
    rfl
  haveI : Nonempty (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) :=
    ⟨⟨specAlgHomPoint χ, trivial⟩⟩
  have hg : ∀ i, (dominantFunctionFieldMap j).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g i))) =
      (Spec (CommRingCat.of (Localization.Away f))).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away f))).inv
          (algebraMap A (Localization.Away f) (g i))) := by
    intro i
    rw [← (Spec (CommRingCat.of A)).algebraMap_germ_eq_germToFunctionField
        (show j (specAlgHomPoint χ) ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial),
      dominantFunctionFieldMap_algebraMap,
      ← (Spec (CommRingCat.of (Localization.Away f))).algebraMap_germ_eq_germToFunctionField
        (show specAlgHomPoint χ ∈ (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
          from trivial)]
    congr 1
    rw [stalkMap_germ_top]
    congr 1
    exact specMap_appTop_ΓSpecIso_inv _ _
  rw [← hpt]
  exact modelThresholdBadAt_openImmersion_iff j cX cXf (specAlgHomPoint χ) _ _ hg M

end Localization

end MixedFujita
