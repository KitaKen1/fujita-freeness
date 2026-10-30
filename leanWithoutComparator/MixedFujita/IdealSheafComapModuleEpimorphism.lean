/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafComapModuleMorphism
public import MixedFujita.AffineCartierDirectImageFactorization
public import MixedFujita.EffectiveCartierIdealSheaf
public import Mathlib.Topology.Sheaves.LocallySurjective

/-! The global canonical ideal-comap map is epimorphic. Actual pulled
sections generate exactly the actual comap ideal on compatible affine
charts. No flatness, dominance, integrality or quasi-coherence is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {B B' : Scheme.{u}}

theorem idealSheafComapModuleMap_pulled_section_coefficient
    (I : B.IdealSheafData) (β : B' ⟶ B) (U : B.Opens) (V : B'.Opens)
    (hVU : V ≤ β ⁻¹ᵁ U) (s : Γ(idealSheafDataModule I, U)) :
    Scheme.Modules.Hom.app (idealSheafDataModuleInclusion (I.comap β)) V
      (Scheme.Modules.Hom.app (idealSheafComapModuleMap I β) V
        (((Scheme.Modules.pullback β).obj (idealSheafDataModule I)).presheaf.map
          (homOfLE hVU).op (modulePullbackSections β (idealSheafDataModule I) U s))) =
      β.appLE U V hVU (Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U s) := by
  change Scheme.Modules.Hom.app
    (idealSheafComapModuleMap I β ≫ idealSheafDataModuleInclusion (I.comap β)) V _ = _
  rw [idealSheafComapModuleMap_inclusion,
    moduleStructureHom_restriction, modulePullbackSections_coefficient]
  rfl

theorem idealSheafComapModuleMap_affine_coefficient_image
    (I : B.IdealSheafData) (β : B' ⟶ B) (U : B.affineOpens) (V : B'.affineOpens)
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    moduleStructureImageIdeal
        (idealSheafComapModuleMap I β ≫ idealSheafDataModuleInclusion (I.comap β)) V.1 =
      (I.comap β).ideal V := by
  apply le_antisymm
  · intro a ha
    obtain ⟨s, rfl⟩ := (mem_moduleStructureImageIdeal _ V.1 a).mp ha
    exact (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image (I.comap β) V) _).mp
      ⟨Scheme.Modules.Hom.app (idealSheafComapModuleMap I β) V.1 s, rfl⟩
  · rw [idealSheaf_comap_affine_chart I β U V hVU]
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    obtain ⟨s, hs⟩ :=
      (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image I U) a).mpr ha
    apply (mem_moduleStructureImageIdeal _ V.1 _).mpr
    refine ⟨((Scheme.Modules.pullback β).obj (idealSheafDataModule I)).presheaf.map
      (homOfLE hVU).op (modulePullbackSections β (idealSheafDataModule I) U.1 s), ?_⟩
    change Scheme.Modules.Hom.app (idealSheafDataModuleInclusion (I.comap β)) V.1
      (Scheme.Modules.Hom.app (idealSheafComapModuleMap I β) V.1 _) = _
    rw [idealSheafComapModuleMap_pulled_section_coefficient, hs]

theorem idealSheafComapModuleMap_affine_app_surjective
    (I : B.IdealSheafData) (β : B' ⟶ B) (U : B.affineOpens) (V : B'.affineOpens)
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) :
    Function.Surjective (Scheme.Modules.Hom.app (idealSheafComapModuleMap I β) V.1) := by
  intro s
  have hm : Scheme.Modules.Hom.app (idealSheafDataModuleInclusion (I.comap β)) V.1 s ∈
      (I.comap β).ideal V :=
    (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image (I.comap β) V) _).mp ⟨s, rfl⟩
  rw [← idealSheafComapModuleMap_affine_coefficient_image I β U V hVU] at hm
  obtain ⟨t, ht⟩ := (mem_moduleStructureImageIdeal _ V.1 _).mp hm
  exact ⟨t, idealSheafDataModuleInclusion_app_injective (I.comap β) V.1 ht⟩

theorem idealSheafComapModuleMap_epi (I : B.IdealSheafData) (β : B' ⟶ B) :
    Epi (idealSheafComapModuleMap I β) := by
  have h : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf B'.ringCatSheaf).map (idealSheafComapModuleMap I β)).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro W s x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := B.isBasis_affineOpens.exists_subset_of_mem_open
      (show β x ∈ (⊤ : B.Opens) from trivial) (⊤ : B.Opens).isOpen
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVs⟩ := B'.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ W ⊓ β ⁻¹ᵁ U from ⟨hx, hxU⟩) (W ⊓ β ⁻¹ᵁ U).isOpen
    have hVW : V ≤ W := hVs.trans inf_le_left
    obtain ⟨t, ht⟩ := idealSheafComapModuleMap_affine_app_surjective I β ⟨U, hU⟩ ⟨V, hV⟩
      (hVs.trans inf_le_right) ((idealSheafDataModule (I.comap β)).presheaf.map (homOfLE hVW).op s)
    exact ⟨V, hVW, ⟨t, ht⟩, hxV⟩
  have : Epi ((SheafOfModules.toSheaf B'.ringCatSheaf).map (idealSheafComapModuleMap I β)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp h
  exact (SheafOfModules.toSheaf B'.ringCatSheaf).epi_of_epi_map inferInstance

end MixedFujita
