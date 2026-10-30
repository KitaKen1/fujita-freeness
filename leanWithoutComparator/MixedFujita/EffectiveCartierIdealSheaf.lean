/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InvertibleAffineDenominators
public import MixedFujita.IdealSheafModuleFunctor

/-!
The image of an actual morphism from an invertible module to the structure
module constructs actual IdealSheafData on any scheme. Denominator clearing
proves the required affine basic-open localization identity. A monic morphism
supplies an actual invertible-ideal presentation without an image assumption.
Every actual effective Cartier divisor on an integral scheme thereby has
actual ideal data, a canonical module comparison and a proved actual
subscheme quotient short exact sequence. Projection formula, cohomology
comparison and pointed complete-intersection existence remain separate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} {M : X.Modules}

noncomputable def moduleStructureImageIdeal
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) : Ideal Γ(X, U) :=
  LinearMap.range (φ.val.app (op U)).hom

theorem mem_moduleStructureImageIdeal
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens) (a : Γ(X, U)) :
    a ∈ moduleStructureImageIdeal φ U ↔ ∃ s : Γ(M, U), Scheme.Modules.Hom.app φ U s = a :=
  Iff.rfl

theorem moduleStructureHom_restriction
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) {U V : X.Opens} (h : V ≤ U)
    (s : Γ(M, U)) :
    Scheme.Modules.Hom.app φ V (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (Scheme.Modules.Hom.app φ U s) :=
  φ.mapPresheaf.naturality_apply (homOfLE h).op s

theorem invertibleModuleStructureImageIdeal_map_basicOpen
    (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) (f : Γ(X, U.1)) :
    (moduleStructureImageIdeal φ U.1).map
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom =
      moduleStructureImageIdeal φ (X.basicOpen f) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    obtain ⟨s, rfl⟩ := (mem_moduleStructureImageIdeal φ U.1 a).mp ha
    exact (mem_moduleStructureImageIdeal φ _ _).mpr
      ⟨M.presheaf.map (homOfLE (X.basicOpen_le f)).op s,
        moduleStructureHom_restriction φ _ s⟩
  · intro a ha
    obtain ⟨s, hs⟩ := (mem_moduleStructureImageIdeal φ _ a).mp ha
    obtain ⟨n, t, ht⟩ := invertibleAffine_clear_denominator M hM U f s
    have hm : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (Scheme.Modules.Hom.app φ U.1 t) ∈
        (moduleStructureImageIdeal φ U.1).map
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
      Ideal.mem_map_of_mem _ ((mem_moduleStructureImageIdeal φ U.1 _).mpr ⟨t, rfl⟩)
    have he : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (Scheme.Modules.Hom.app φ U.1 t) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n * a := by
      rw [← moduleStructureHom_restriction φ _ t, ht, Scheme.Modules.Hom.app_smul]
      rw [hs]
      rfl
    rw [he] at hm
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) := by
      have := U.2.isLocalization_basicOpen f
      change IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) f)
      exact IsLocalization.Away.algebraMap_isUnit f
    exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow n)).mp hm

noncomputable def invertibleModuleImageIdealSheaf
    (M : X.Modules) (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData where
  ideal U := moduleStructureImageIdeal φ U.1
  map_ideal_basicOpen U f := invertibleModuleStructureImageIdeal_map_basicOpen hM φ U f

theorem invertibleModuleImageIdealSheaf_affine_image
    (M : X.Modules) (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) :
    Set.range (Scheme.Modules.Hom.app φ U.1) =
      ((invertibleModuleImageIdealSheaf M hM φ).ideal U : Set Γ(X, U.1)) := rfl

noncomputable def invertibleModuleImageIdealPresentation
    (M : X.Modules) (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M)
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] :
    InvertibleIdealPresentation (invertibleModuleImageIdealSheaf M hM φ) where
  moduleSheaf := M
  invertible := hM
  inclusion := φ
  injective U := by
    have : Mono ((moduleOpenEvaluation X U).map φ) := (moduleOpenEvaluation X U).map_mono φ
    exact (ModuleCat.mono_iff_injective _).mp this
  image_eq := invertibleModuleImageIdealSheaf_affine_image M hM φ

variable [IsIntegral X]

noncomputable def effectiveCartierIdealSheaf (D : CartierDivisor X) (hD : D.IsEffective) :
    X.IdealSheafData :=
  invertibleModuleImageIdealSheaf (-D).sheaf (-D).isInvertible_sheaf
    (negativeCartierToUnit X D hD)

theorem effectiveCartierIdealSheaf_affine_image
    (D : CartierDivisor X) (hD : D.IsEffective) (U : X.affineOpens) :
    Set.range (Scheme.Modules.Hom.app (negativeCartierToUnit X D hD) U.1) =
      ((effectiveCartierIdealSheaf D hD).ideal U : Set Γ(X, U.1)) := rfl

noncomputable def effectiveCartierIdealPresentation
    (D : CartierDivisor X) (hD : D.IsEffective) :
    InvertibleIdealPresentation (effectiveCartierIdealSheaf D hD) :=
  invertibleModuleImageIdealPresentation (-D).sheaf (-D).isInvertible_sheaf
    (negativeCartierToUnit X D hD)

noncomputable def effectiveCartierIdealModuleIso
    (D : CartierDivisor X) (hD : D.IsEffective) :
    (-D).sheaf ≅ idealSheafDataModule (effectiveCartierIdealSheaf D hD) :=
  invertibleIdealPresentationCanonicalIso (effectiveCartierIdealPresentation D hD)

@[reassoc (attr := simp)]
theorem effectiveCartierIdealModuleIso_hom_inclusion
    (D : CartierDivisor X) (hD : D.IsEffective) :
    (effectiveCartierIdealModuleIso D hD).hom ≫
      idealSheafDataModuleInclusion (effectiveCartierIdealSheaf D hD) =
        negativeCartierToUnit X D hD :=
  invertibleIdealPresentationCanonicalIso_hom_inclusion _

theorem effectiveCartierIdealModule_isInvertible
    (D : CartierDivisor X) (hD : D.IsEffective) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X
      (idealSheafDataModule (effectiveCartierIdealSheaf D hD)) :=
  idealSheafDataModule_isInvertible_of_presentation (effectiveCartierIdealPresentation D hD)

noncomputable def effectiveCartierQuotientShortComplex
    (D : CartierDivisor X) (hD : D.IsEffective) : ShortComplex X.Modules :=
  invertibleIdealSubschemeShortComplex (effectiveCartierIdealPresentation D hD)

theorem effectiveCartierQuotientShortComplex_shortExact
    (D : CartierDivisor X) (hD : D.IsEffective) :
    (effectiveCartierQuotientShortComplex D hD).ShortExact :=
  invertibleIdealSubschemeShortComplex_shortExact _

theorem effectiveCartierIdealSheaf_projective_eq
    {n : ℕ} (R : Type u) [CommRing R] [IsDomain R] (k₀ : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (h0 : f ≠ 0) :
    letI := polynomialProjectiveScheme_isIntegral R k₀
    effectiveCartierIdealSheaf (projectiveHomogeneousCartier R k₀ d f hf h0)
      (projectiveHomogeneousCartier_isEffective R k₀ d f hf h0) =
        projectiveHypersurfaceIdealSheaf f d hf := by
  let := polynomialProjectiveScheme_isIntegral R k₀
  apply Scheme.IdealSheafData.ext
  funext U
  apply SetLike.coe_injective
  exact (effectiveCartierIdealSheaf_affine_image _ _ U).symm.trans
    (projectiveHomogeneousCartier_inclusion_range R k₀ d f hf h0 U)

end MixedFujita
