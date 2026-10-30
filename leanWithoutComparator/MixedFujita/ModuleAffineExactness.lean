/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness

/-!
Detect actual scheme-module morphisms and short exact sequences on the affine
open basis. Kernels are preserved by evaluation; the kernel comparison is an
isomorphism, and an affine basis detects the resulting global isomorphism.
Surjectivity is required only on affine opens, not on arbitrary open sections.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {X : Scheme.{u}}

noncomputable def moduleOpenEvaluation (X : Scheme.{u}) (U : X.Opens) :
    X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)

instance moduleOpenEvaluation_additive (X : Scheme.{u}) (U : X.Opens) :
    (moduleOpenEvaluation X U).Additive where
  map_add := rfl

instance moduleOpenEvaluation_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens) :
    (moduleOpenEvaluation X U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance moduleOpenEvaluation_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (moduleOpenEvaluation X U) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)))

theorem moduleHom_ext_affine {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ U : X.affineOpens, Scheme.Modules.Hom.app f U.1 =
      Scheme.Modules.Hom.app g U.1) : f = g := by
  apply (Scheme.Modules.toPresheaf X).map_injective
  apply TopCat.Sheaf.hom_ext M.presheaf
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)
    (B := fun U : X.affineOpens ↦ U.1)
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
  exact h

theorem moduleHom_isIso_of_affine_app_bijective {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Bijective (Scheme.Modules.Hom.app f U.1)) :
    IsIso f := by
  have : IsIso ((SheafOfModules.toSheaf X.ringCatSheaf).map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis
      (B := fun U : X.affineOpens ↦ U.1)
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using X.isBasis_affineOpens)
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr (h U)
  have : Mono f := (SheafOfModules.toSheaf X.ringCatSheaf).mono_of_mono_map inferInstance
  have : Epi f := (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi f

theorem moduleHom_epi_of_affine_app_surjective {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Surjective (Scheme.Modules.Hom.app f U.1)) :
    Epi f := by
  constructor
  intro P g k hgk
  apply moduleHom_ext_affine
  intro U
  ext s
  obtain ⟨t, rfl⟩ := h U s
  have e := congrArg (fun a : M ⟶ P ↦ Scheme.Modules.Hom.app a U.1 t) hgk
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using e

theorem moduleHom_mono_of_affine_app_injective {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Injective (Scheme.Modules.Hom.app f U.1)) :
    Mono f := by
  constructor
  intro P g k hgk
  apply moduleHom_ext_affine
  intro U
  ext s
  apply h U
  have e := congrArg (fun a : P ⟶ N ↦ Scheme.Modules.Hom.app a U.1 s) hgk
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using e

theorem moduleShortComplex_shortExact_of_affine_evaluation
    (S : ShortComplex X.Modules)
    (h : ∀ U : X.affineOpens,
      (S.map (moduleOpenEvaluation X U.1)).ShortExact) :
    S.ShortExact := by
  have hf : Mono S.f := moduleHom_mono_of_affine_app_injective S.f fun U ↦ by
    change Function.Injective ((moduleOpenEvaluation X U.1).map S.f)
    exact (ModuleCat.mono_iff_injective _).mp (h U).mono_f
  have hg : Epi S.g := moduleHom_epi_of_affine_app_surjective S.g fun U ↦ by
    change Function.Surjective ((moduleOpenEvaluation X U.1).map S.g)
    exact (ModuleCat.epi_iff_surjective _).mp (h U).epi_g
  have ht : IsIso (kernel.lift S.g S.f S.zero) := by
    apply moduleHom_isIso_of_affine_app_bijective
    intro U
    let F := moduleOpenEvaluation X U.1
    let T := S.map F
    have hT : T.ShortExact := h U
    have : Mono (kernel.lift T.g T.f T.zero) :=
      @mono_of_mono_fac _ _ _ _ _ _ _ _ hT.mono_f (kernel.lift_ι T.g T.f T.zero)
    have := hT.exact.epi_kernelLift
    have : IsIso (kernel.lift T.g T.f T.zero) := isIso_of_mono_of_epi _
    have : IsIso (F.map (kernel.lift S.g S.f S.zero) ≫ kernelComparison S.g F) := by
      rw [map_lift_kernelComparison]
      exact inferInstanceAs (IsIso (kernel.lift T.g T.f T.zero))
    have : IsIso (F.map (kernel.lift S.g S.f S.zero)) :=
      IsIso.of_isIso_comp_right _ (kernelComparison S.g F)
    exact ConcreteCategory.bijective_of_isIso (F.map (kernel.lift S.g S.f S.zero))
  exact ShortComplex.ShortExact.mk' (S.exact_iff_epi_kernel_lift.mpr inferInstance) hf hg

end MixedFujita
