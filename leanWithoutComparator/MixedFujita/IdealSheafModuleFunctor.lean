/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InvertibleIdealQuotientSequence

/-!
Every actual IdealSheafData has a canonical actual module sheaf: the kernel
of O_X -> i_* O_Z for its actual associated subscheme. Its inclusion has
exactly the given ideal as image on every affine open. Ideal inclusions give
module morphisms and a functor, and the canonical quotient sequence is proved
short exact. This is not a cohomology comparison with Z or a Bertini theorem.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}}

noncomputable def idealSheafDataModule (I : X.IdealSheafData) : X.Modules :=
  kernel (schemeUnitToPushforwardUnit I.subschemeι)

noncomputable def idealSheafDataModuleInclusion (I : X.IdealSheafData) :
    idealSheafDataModule I ⟶ SheafOfModules.unit X.ringCatSheaf :=
  kernel.ι (schemeUnitToPushforwardUnit I.subschemeι)

instance idealSheafDataModuleInclusion_mono (I : X.IdealSheafData) :
    Mono (idealSheafDataModuleInclusion I) :=
  inferInstanceAs (Mono (kernel.ι (schemeUnitToPushforwardUnit I.subschemeι)))

noncomputable def idealSheafDataModuleQuotientSequence (I : X.IdealSheafData) :
    ShortComplex X.Modules :=
  ShortComplex.mk (idealSheafDataModuleInclusion I) (schemeUnitToPushforwardUnit I.subschemeι)
    (kernel.condition _)

theorem idealSheafDataModuleQuotientSequence_shortExact (I : X.IdealSheafData) :
    (idealSheafDataModuleQuotientSequence I).ShortExact := by
  have hg : Epi (schemeUnitToPushforwardUnit I.subschemeι) :=
    moduleHom_epi_of_affine_app_surjective _ fun U ↦ I.subschemeι_app_surjective U
  have hf : Mono (idealSheafDataModuleInclusion I) := inferInstance
  apply ShortComplex.ShortExact.mk' _ hf hg
  exact (idealSheafDataModuleQuotientSequence I).exact_of_f_is_kernel
    (kernelIsKernel (schemeUnitToPushforwardUnit I.subschemeι))

theorem idealSheafDataModuleInclusion_affine_image
    (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1) =
      (I.ideal U : Set Γ(X, U.1)) := by
  let S := idealSheafDataModuleQuotientSequence I
  have hS : S.ShortExact := idealSheafDataModuleQuotientSequence_shortExact I
  have := hS.mono_f
  let F := moduleOpenEvaluation X U.1
  have he := (ShortComplex.moduleCat_exact_iff_range_eq_ker (S.map F)).mp
    (hS.exact.map_of_mono_of_preservesKernel F hS.mono_f inferInstance)
  ext a
  change a ∈ LinearMap.range ((S.map F).f).hom ↔ a ∈ I.ideal U
  rw [he]
  change I.subschemeι.app U.1 a = 0 ↔ a ∈ I.ideal U
  rw [← I.ker_subschemeι_app U]
  rfl

theorem idealSheafDataModuleInclusion_comp_quotient_of_le
    {I J : X.IdealSheafData} (h : I ≤ J) :
    idealSheafDataModuleInclusion I ≫ schemeUnitToPushforwardUnit J.subschemeι = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext s
  change J.subschemeι.app U.1
    (Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1 s) = 0
  have hi : Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1 s ∈ I.ideal U :=
    (Set.ext_iff.mp (idealSheafDataModuleInclusion_affine_image I U) _).mp ⟨s, rfl⟩
  have hj : Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1 s ∈ J.ideal U :=
    h U hi
  rw [← J.ker_subschemeι_app U] at hj
  exact hj

noncomputable def idealSheafDataModuleMap {I J : X.IdealSheafData} (h : I ≤ J) :
    idealSheafDataModule I ⟶ idealSheafDataModule J :=
  kernel.lift (schemeUnitToPushforwardUnit J.subschemeι) (idealSheafDataModuleInclusion I)
    (idealSheafDataModuleInclusion_comp_quotient_of_le h)

@[reassoc (attr := simp)]
theorem idealSheafDataModuleMap_inclusion {I J : X.IdealSheafData} (h : I ≤ J) :
    idealSheafDataModuleMap h ≫ idealSheafDataModuleInclusion J =
      idealSheafDataModuleInclusion I := kernel.lift_ι _ _ _

theorem idealSheafDataModuleMap_id (I : X.IdealSheafData) :
    idealSheafDataModuleMap (le_refl I) = 𝟙 (idealSheafDataModule I) := by
  apply (cancel_mono (idealSheafDataModuleInclusion I)).mp
  simp

theorem idealSheafDataModuleMap_comp {I J K : X.IdealSheafData}
    (h : I ≤ J) (k : J ≤ K) :
    idealSheafDataModuleMap h ≫ idealSheafDataModuleMap k =
      idealSheafDataModuleMap (h.trans k) := by
  apply (cancel_mono (idealSheafDataModuleInclusion K)).mp
  simp only [Category.assoc, idealSheafDataModuleMap_inclusion]

noncomputable def idealSheafDataToModuleFunctor (X : Scheme.{u}) :
    X.IdealSheafData ⥤ X.Modules where
  obj := idealSheafDataModule
  map h := idealSheafDataModuleMap (leOfHom h)
  map_id I := idealSheafDataModuleMap_id I
  map_comp h k := (idealSheafDataModuleMap_comp (leOfHom h) (leOfHom k)).symm

noncomputable def idealSheafDataModuleInclusionNatTrans (X : Scheme.{u}) :
    idealSheafDataToModuleFunctor X ⟶
      (Functor.const X.IdealSheafData).obj (SheafOfModules.unit X.ringCatSheaf) where
  app I := idealSheafDataModuleInclusion I
  naturality := by
    intro I J h
    change idealSheafDataModuleMap (leOfHom h) ≫ idealSheafDataModuleInclusion J =
      idealSheafDataModuleInclusion I ≫ 𝟙 _
    rw [Category.comp_id]
    exact idealSheafDataModuleMap_inclusion (leOfHom h)

theorem idealSheafDataModuleMap_mono {I J : X.IdealSheafData} (h : I ≤ J) :
    Mono (idealSheafDataModuleMap h) :=
  mono_of_mono_fac (idealSheafDataModuleMap_inclusion h)

theorem idealSheafDataModuleInclusion_app_injective (I : X.IdealSheafData) (U : X.Opens) :
    Function.Injective (Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U) := by
  have : Mono ((moduleOpenEvaluation X U).map (idealSheafDataModuleInclusion I)) :=
    (moduleOpenEvaluation X U).map_mono _
  exact (ModuleCat.mono_iff_injective _).mp this

noncomputable def invertibleIdealPresentationCanonicalIso {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) : P.moduleSheaf ≅ idealSheafDataModule I :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι (kernel.ι (schemeUnitToPushforwardUnit I.subschemeι))
      (kernel.condition _))
    (invertibleIdealSubschemeShortComplex_shortExact P).fIsKernel
    (kernelIsKernel (schemeUnitToPushforwardUnit I.subschemeι))

@[reassoc (attr := simp)]
theorem invertibleIdealPresentationCanonicalIso_hom_inclusion {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    (invertibleIdealPresentationCanonicalIso P).hom ≫ idealSheafDataModuleInclusion I =
      P.inclusion :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (invertibleIdealSubschemeShortComplex_shortExact P).fIsKernel
    (kernelIsKernel (schemeUnitToPushforwardUnit I.subschemeι)) WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem invertibleIdealPresentationCanonicalIso_inv_inclusion {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    (invertibleIdealPresentationCanonicalIso P).inv ≫ P.inclusion =
      idealSheafDataModuleInclusion I :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (invertibleIdealSubschemeShortComplex_shortExact P).fIsKernel
    (kernelIsKernel (schemeUnitToPushforwardUnit I.subschemeι)) WalkingParallelPair.zero

theorem idealSheafDataModule_isInvertible_of_presentation {I : X.IdealSheafData}
    (P : InvertibleIdealPresentation I) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (idealSheafDataModule I) :=
  (TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X).prop_of_iso
    (invertibleIdealPresentationCanonicalIso P) P.invertible

noncomputable def canonicalInvertibleIdealPresentation (I : X.IdealSheafData)
    (hI : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (idealSheafDataModule I)) :
    InvertibleIdealPresentation I where
  moduleSheaf := idealSheafDataModule I
  invertible := hI
  inclusion := idealSheafDataModuleInclusion I
  injective := idealSheafDataModuleInclusion_app_injective I
  image_eq := idealSheafDataModuleInclusion_affine_image I

theorem idealSheafDataModule_isInvertible_iff_nonempty_presentation (I : X.IdealSheafData) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (idealSheafDataModule I) ↔
      Nonempty (InvertibleIdealPresentation I) :=
  ⟨fun h ↦ ⟨canonicalInvertibleIdealPresentation I h⟩,
    fun ⟨P⟩ ↦ idealSheafDataModule_isInvertible_of_presentation P⟩

end MixedFujita
