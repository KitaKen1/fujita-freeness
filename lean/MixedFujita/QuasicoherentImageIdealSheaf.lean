/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierIdealSheaf

/-! Extend the actual image-ideal construction from invertible modules
to arbitrary quasicoherent modules. Monomorphisms identify their source with
the actual ideal module, without assuming that source invertible. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}}

theorem quasicoherentAffine_clear_denominator (M : X.Modules) [M.IsQuasicoherent]
    (U : X.affineOpens) (f : Γ(X, U.1)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U.1)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  let N := M.restrict U.2.fromSpec
  obtain ⟨n, t, ht⟩ := quasicoherentSpec_clear_denominator N f
    ((moduleAffineBasicOpenIso M U f).inv s)
  refine ⟨n, (moduleAffineTopIso M U).hom t, ?_⟩
  have h := congrArg (moduleAffineBasicOpenIso M U f).hom ht
  rw [moduleAffineBasicOpenIso_restriction, moduleAffineBasicOpenIso_smul,
    map_pow, Iso.inv_hom_id_apply] at h
  exact h

variable {M : X.Modules} [M.IsQuasicoherent]

theorem quasicoherentModuleStructureImageIdeal_map_basicOpen
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
    obtain ⟨n, t, ht⟩ := quasicoherentAffine_clear_denominator M U f s
    have hm : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (Scheme.Modules.Hom.app φ U.1 t) ∈
        (moduleStructureImageIdeal φ U.1).map
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
      Ideal.mem_map_of_mem _ ((mem_moduleStructureImageIdeal φ U.1 _).mpr ⟨t, rfl⟩)
    have he : X.presheaf.map (homOfLE (X.basicOpen_le f)).op
        (Scheme.Modules.Hom.app φ U.1 t) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n * a := by
      rw [← moduleStructureHom_restriction φ _ t, ht, Scheme.Modules.Hom.app_smul, hs]
      rfl
    rw [he] at hm
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) := by
      have := U.2.isLocalization_basicOpen f
      change IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f) f)
      exact IsLocalization.Away.algebraMap_isUnit f
    exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow n)).mp hm

noncomputable def quasicoherentModuleImageIdealSheaf
    (M : X.Modules) [M.IsQuasicoherent]
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData where
  ideal U := moduleStructureImageIdeal φ U.1
  map_ideal_basicOpen U f := quasicoherentModuleStructureImageIdeal_map_basicOpen φ U f

theorem quasicoherentModuleImageIdealSheaf_affine_image
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) :
    Set.range (Scheme.Modules.Hom.app φ U.1) =
      ((quasicoherentModuleImageIdealSheaf M φ).ideal U : Set Γ(X, U.1)) := rfl

theorem quasicoherentImageIdeal_quotient_comp_zero
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    φ ≫ schemeUnitToPushforwardUnit (quasicoherentModuleImageIdealSheaf M φ).subschemeι = 0 := by
  apply moduleHom_ext_affine
  intro U
  ext s
  let I := quasicoherentModuleImageIdealSheaf M φ
  change I.subschemeι.app U.1 (Scheme.Modules.Hom.app φ U.1 s) = 0
  have hm : Scheme.Modules.Hom.app φ U.1 s ∈ I.ideal U := ⟨s, rfl⟩
  rw [← I.ker_subschemeι_app U] at hm
  exact hm

noncomputable def quasicoherentImageIdealShortComplex
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) : ShortComplex X.Modules :=
  ShortComplex.mk φ
    (schemeUnitToPushforwardUnit (quasicoherentModuleImageIdealSheaf M φ).subschemeι)
    (quasicoherentImageIdeal_quotient_comp_zero φ)

theorem quasicoherentImageIdealShortComplex_shortExact
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] :
    (quasicoherentImageIdealShortComplex φ).ShortExact := by
  apply moduleShortComplex_shortExact_of_affine_evaluation
  intro U
  let I := quasicoherentModuleImageIdealSheaf M φ
  let S := (quasicoherentImageIdealShortComplex φ).map (moduleOpenEvaluation X U.1)
  have hf : Mono S.f := (moduleOpenEvaluation X U.1).map_mono φ
  have hg : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr (I.subschemeι_app_surjective U)
  apply ShortComplex.ShortExact.mk' (S := S) _ hf hg
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hm : a ∈ I.ideal U := by
    rw [← I.ker_subschemeι_app U]
    exact ha
  exact hm

noncomputable def quasicoherentImageIdealModuleIso
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] :
    M ≅ idealSheafDataModule (quasicoherentModuleImageIdealSheaf M φ) :=
  IsLimit.conePointUniqueUpToIso
    (t := KernelFork.ofι
      (kernel.ι (schemeUnitToPushforwardUnit (quasicoherentModuleImageIdealSheaf M φ).subschemeι))
      (kernel.condition _))
    (quasicoherentImageIdealShortComplex_shortExact φ).fIsKernel
    (kernelIsKernel _)

@[reassoc (attr := simp)]
theorem quasicoherentImageIdealModuleIso_hom_inclusion
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] :
    (quasicoherentImageIdealModuleIso φ).hom ≫
      idealSheafDataModuleInclusion (quasicoherentModuleImageIdealSheaf M φ) = φ :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (quasicoherentImageIdealShortComplex_shortExact φ).fIsKernel
    (kernelIsKernel _) WalkingParallelPair.zero

@[reassoc (attr := simp)]
theorem quasicoherentImageIdealModuleIso_inv_inclusion
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] :
    (quasicoherentImageIdealModuleIso φ).inv ≫ φ =
      idealSheafDataModuleInclusion (quasicoherentModuleImageIdealSheaf M φ) :=
  IsLimit.conePointUniqueUpToIso_inv_comp
    (quasicoherentImageIdealShortComplex_shortExact φ).fIsKernel
    (kernelIsKernel _) WalkingParallelPair.zero

end MixedFujita
