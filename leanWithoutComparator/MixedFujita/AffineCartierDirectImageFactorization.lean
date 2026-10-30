/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.IdealSheafAffineModulePresentation
public import MixedFujita.AffineOpenIdealPullback

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem idealSheaf_comap_fromSpec {B : Scheme.{u}} (I : B.IdealSheafData)
    (U : B.affineOpens) :
    I.comap U.2.fromSpec = specIdealSheaf (I.ideal U) := by
  letI : IsAffine U.1.toScheme := U.2
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [IsAffineOpen.fromSpec, Scheme.IdealSheafData.comap_comp,
    affineIdealSheaf_comap_top, idealSheaf_affineOpen_restrict_top,
    specIdealSheaf_ideal_top, Ideal.map_map]
  simp only [← CommRingCat.hom_comp, IsAffineOpen.isoSpec_inv_appTop,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rfl

theorem idealSheaf_comap_affine_chart {B B' : Scheme.{u}}
    (I : B.IdealSheafData) (β : B' ⟶ B) (U : B.affineOpens) (V : B'.affineOpens)
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    (I.comap β).ideal V = (I.ideal U).map (β.appLE U.1 V.1 hVU).hom := by
  apply specIdealSheaf_injective Γ(B', V.1)
  rw [← idealSheaf_comap_fromSpec, ← Scheme.IdealSheafData.comap_comp,
    ← IsAffineOpen.SpecMap_appLE_fromSpec β U.2 V.2 hVU,
    Scheme.IdealSheafData.comap_comp, idealSheaf_comap_fromSpec]
  exact specIdealSheaf_comap (I.ideal U) (β.appLE U.1 V.1 hVU).hom

theorem dominant_affine_chart_coefficients_injective
    {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B']
    (β : B' ⟶ B) [IsDominant β] (U : B.affineOpens) (V : B'.affineOpens)
    [Nonempty V.1] (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    Function.Injective (β.appLE U.1 V.1 hVU).hom := by
  letI : Nonempty U.1 := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V.1)
    exact ⟨⟨β v.1, hVU v.property⟩⟩
  intro a b hab
  apply B.germToFunctionField_injective U.1
  apply (dominantFunctionFieldMap β).hom.injective
  rw [dominantFunctionFieldMap_germ β U.1 V.1 hVU,
    dominantFunctionFieldMap_germ β U.1 V.1 hVU, hab]

theorem cartier_direct_image_affine_spec_sections_noZeroSMulDivisors
    {T B : Scheme.{u}} [IsIntegral T] [IsIntegral B]
    (q : T ⟶ B) [IsDominant q] (E : CartierDivisor T) (V : B.affineOpens) :
    NoZeroSMulDivisors Γ(B, V.1)
      ((moduleSpecΓFunctor (R := Γ(B, V.1))).obj
        (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec)) := by
  let F := (Scheme.Modules.pushforward q).obj E.sheaf
  letI := cartier_direct_image_sections_noZeroSMulDivisors q E V.1
  let e := moduleAffineSectionsLinearEquiv F V
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero
    (fun r s ↦ e.map_smul r s)

/-- On any actual pair of compatible nonempty affine charts, the coefficient
map's injectivity, ideal nonvanishing and Cartier target torsion-freeness are
all derived from the original geometric witnesses. -/
theorem actual_affine_changed_cartier_direct_image_existsUnique_ideal_factor
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T) (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1)
    (ψ : (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).obj
        ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶
      (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec)) :
    ∃! δ : tilde (ModuleCat.of Γ(B', V.1) ((I.ideal U).map (β.appLE U.1 V.1 hVU).hom)) ⟶
        (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec),
      affineIdealModulePullbackImageMap I U (β.appLE U.1 V.1 hVU) ≫ δ = ψ := by
  letI : Nonempty U.1 := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V.1)
    exact ⟨⟨β v.1, hVU v.property⟩⟩
  letI := cartier_direct_image_affine_spec_sections_noZeroSMulDivisors q E V
  exact affineIdealModulePullbackImageMap_existsUnique_factor I U _
    (idealSheafData_affine_ideal_ne_bot I hI U)
    (dominant_affine_chart_coefficients_injective β U V hVU) _ ψ

/-- The associated extended ideal is the actual canonical comap ideal module
on the target chart, with no passage to radicals. -/
noncomputable def affineIdealComapSpecIso {B B' : Scheme.{u}}
    (I : B.IdealSheafData) (β : B' ⟶ B)
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    tilde (ModuleCat.of Γ(B', V.1) ((I.ideal U).map (β.appLE U.1 V.1 hVU).hom)) ≅
      (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec :=
  (tilde.functor Γ(B', V.1)).mapIso
      (LinearEquiv.ofEq _ _ (idealSheaf_comap_affine_chart I β U V hVU).symm).toModuleIso ≪≫
    (idealSheafDataModuleAffineSpecIso (I.comap β) V).symm

noncomputable def actualAffineIdealComapImageMap {B B' : Scheme.{u}}
    (I : B.IdealSheafData) (β : B' ⟶ B)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).obj
        ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶
      (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec :=
  affineIdealModulePullbackImageMap I U (β.appLE U.1 V.1 hVU) ≫
    (affineIdealComapSpecIso I β U V hVU).hom

theorem actualAffineIdealComapImageMap_epi {B B' : Scheme.{u}}
    (I : B.IdealSheafData) (β : B' ⟶ B)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    Epi (actualAffineIdealComapImageMap I β U V hVU) := by
  letI := affineIdealModulePullbackImageMap_epi I U (β.appLE U.1 V.1 hVU)
  unfold actualAffineIdealComapImageMap
  infer_instance

/-- The local factorization is now through the actual canonical module of
I.comap β. Quasi-coherence of the two ideal modules suffices; no invertibility or
flatness input is needed. Gluing these actual chart maps is still separate. -/
theorem actual_affine_changed_cartier_direct_image_existsUnique_comap_factor
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T) (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1)
    (ψ : (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).obj
        ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶
      (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec)) :
    ∃! δ : (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec ⟶
        (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec),
      actualAffineIdealComapImageMap I β U V hVU ≫ δ = ψ := by
  let e := affineIdealComapSpecIso I β U V hVU
  obtain ⟨δ, hδ, _⟩ := actual_affine_changed_cartier_direct_image_existsUnique_ideal_factor
    β q E I hI U V hVU ψ
  have hfac : actualAffineIdealComapImageMap I β U V hVU ≫ (e.inv ≫ δ) = ψ := by
    change (affineIdealModulePullbackImageMap I U (β.appLE U.1 V.1 hVU) ≫ e.hom) ≫
      (e.inv ≫ δ) = ψ
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hδ
  letI := actualAffineIdealComapImageMap_epi I β U V hVU
  exact ⟨e.inv ≫ δ, hfac, fun δ' hδ' ↦
    (cancel_epi (actualAffineIdealComapImageMap I β U V hVU)).mp (hδ'.trans hfac.symm)⟩

/-- The genuine chart comparison for the pullback of an arbitrary actual
scheme module, using the actual commuting chart square. -/
noncomputable def affineChartPullbackRestrictionIso {B B' : Scheme.{u}}
    (β : B' ⟶ B) (F : B.Modules) (U : B.affineOpens) (V : B'.affineOpens)
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).obj
        (F.restrict U.2.fromSpec) ≅
      ((Scheme.Modules.pullback β).obj F).restrict V.2.fromSpec :=
  (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app F) ≪≫
    (Scheme.Modules.pullbackComp (Spec.map (β.appLE U.1 V.1 hVU)) U.2.fromSpec).app F ≪≫
    (Scheme.Modules.pullbackCongr (IsAffineOpen.SpecMap_appLE_fromSpec β U.2 V.2 hVU)).app F ≪≫
    ((Scheme.Modules.pullbackComp V.2.fromSpec β).app F).symm ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback V.2.fromSpec).app
      ((Scheme.Modules.pullback β).obj F)).symm

/-- Every actual global comparison map has a unique factor on each compatible
nonempty affine chart through the actual comap ideal module. The source
comparison is constructed from the actual chart square, rather than supplied. -/
theorem actual_global_cartier_direct_image_map_affine_comap_factor
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T) (I : B.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (ψ : (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf)
    (U : B.affineOpens) (V : B'.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    ∃! δ : (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec ⟶
        (((Scheme.Modules.pushforward q).obj E.sheaf).restrict V.2.fromSpec),
      actualAffineIdealComapImageMap I β U V hVU ≫ δ =
        (affineChartPullbackRestrictionIso β (idealSheafDataModule I) U V hVU).hom ≫
          (Scheme.Modules.restrictFunctor V.2.fromSpec).map ψ :=
  actual_affine_changed_cartier_direct_image_existsUnique_comap_factor β q E I hI U V hVU _

end MixedFujita
