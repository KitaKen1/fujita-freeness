/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafModuleFunctor
public import MixedFujita.SpecIdealPullbackFactorization
public import MixedFujita.CartierDirectImageTorsionFree
public import MixedFujita.CanonicalImageIdealNonvanishing
public import SGA.Foundations.Cohomology.AffineOpenVanishing
public import SGA.Foundations.Cohomology.Helpers
public import SGA.Foundations.QuasiCoherent.SpecSections

/-! Identify the canonical kernel module of actual ideal-sheaf data with
the associated module of its actual affine ideal. The resulting presentation
connects actual scheme modules to the nonflat Spec ideal-factorization lemma.
Quasi-coherence is used only for the affine sheaf presentation. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}}

/-- Restricting to an affine chart identifies its Spec global-section module
linearly, over the actual affine ring, with the original module's sections. -/
noncomputable def moduleAffineSectionsLinearEquiv (F : X.Modules) (U : X.affineOpens) :
    (F.restrict U.2.fromSpec).ΓSpec ≃ₗ[Γ(X, U.1)] Γ(F, U.1) := by
  have hW : ⊤ ⊓ U.1 = U.2.fromSpec ''ᵁ ⊤ := by
    rw [top_inf_eq, Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
  let res : (F.presheafInf U.1).obj (op ⊤) →ₗ[Γ(X, U.1)] Γ(F, U.1) :=
    { toFun := fun s ↦ F.presheaf.map (homOfLE (le_inf le_top le_rfl : U.1 ≤ ⊤ ⊓ U.1)).op s
      map_add' := fun _ _ ↦ map_add _ _ _
      map_smul' := fun r s ↦ by
        change F.presheaf.map (homOfLE (le_inf le_top le_rfl : U.1 ≤ ⊤ ⊓ U.1)).op
            (X.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ U.1 ≤ U.1)).op r •
              @id Γ(F, ⊤ ⊓ U.1) s) = r • _
        rw [Scheme.Modules.map_smul, CohomologyAux.presheaf_map_map,
          CohomologyAux.presheaf_map_self]
        rfl }
  have hres : Function.Bijective res := by
    have hr : Function.LeftInverse
        (fun t ↦ F.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ U.1 ≤ U.1)).op t) res := by
      intro s
      change F.presheaf.map _ (F.presheaf.map _ (@id Γ(F, ⊤ ⊓ U.1) s)) = s
      rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
      rfl
    refine ⟨hr.injective, fun t ↦ ⟨F.presheaf.map
      (homOfLE (inf_le_right : ⊤ ⊓ U.1 ≤ U.1)).op t, ?_⟩⟩
    change F.presheaf.map _ (F.presheaf.map _ t) = t
    rw [TopCat.Presheaf.map_map_apply, CohomologyAux.modules_map_self]
  exact (LinearEquiv.ofBijective (F.restrictFromSpecₗ U.2 ⊤ ⊤ hW.le)
    (F.bijective_restrictFromSpecₗ U.2 ⊤ ⊤ hW)).trans
      (LinearEquiv.ofBijective res hres)

/-- Affine presentation using the original module's actual sections. -/
noncomputable def moduleAffineTildeIso (F : X.Modules) [F.IsQuasicoherent]
    (U : X.affineOpens) :
    F.restrict U.2.fromSpec ≅ tilde (ModuleCat.of Γ(X, U.1) Γ(F, U.1)) := by
  let G := F.restrict U.2.fromSpec
  letI : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback U.2.fromSpec).app F).symm
  exact G.tildeΓIso.symm ≪≫
    (tilde.functor Γ(X, U.1)).mapIso (moduleAffineSectionsLinearEquiv F U).toModuleIso

/-- The inclusion of the canonical kernel module identifies its sections
with the actual ideal, with no supplied ideal-module presentation. -/
noncomputable def idealSheafDataModuleAffineSectionsEquiv (I : X.IdealSheafData)
    (U : X.affineOpens) :
    Γ(idealSheafDataModule I, U.1) ≃ₗ[Γ(X, U.1)] I.ideal U := by
  let f := ((moduleOpenEvaluation X U.1).map (idealSheafDataModuleInclusion I)).hom
  have hinj : Function.Injective f := idealSheafDataModuleInclusion_app_injective I U.1
  have hr : LinearMap.range f = I.ideal U := by
    apply SetLike.coe_injective
    exact idealSheafDataModuleInclusion_affine_image I U
  exact (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hr)

theorem idealSheafDataModuleAffineSectionsEquiv_coe (I : X.IdealSheafData)
    (U : X.affineOpens) (s : Γ(idealSheafDataModule I, U.1)) :
    (idealSheafDataModuleAffineSectionsEquiv I U s : Γ(X, U.1)) =
      Scheme.Modules.Hom.app (idealSheafDataModuleInclusion I) U.1 s := rfl

/-- The actual canonical ideal module on an affine chart is the associated
sheaf of the given affine ideal. -/
noncomputable def idealSheafDataModuleAffineSpecIso (I : X.IdealSheafData)
    [(idealSheafDataModule I).IsQuasicoherent] (U : X.affineOpens) :
    (idealSheafDataModule I).restrict U.2.fromSpec ≅
      tilde (ModuleCat.of Γ(X, U.1) (I.ideal U)) :=
  moduleAffineTildeIso (idealSheafDataModule I) U ≪≫
    (tilde.functor Γ(X, U.1)).mapIso
      (idealSheafDataModuleAffineSectionsEquiv I U).toModuleIso

/-- Pull back the actual canonical ideal module on a chart, then map to the
associated sheaf of the actual extended ideal. -/
noncomputable def affineIdealModulePullbackImageMap (I : X.IdealSheafData)
    [(idealSheafDataModule I).IsQuasicoherent] (U : X.affineOpens)
    {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    (Scheme.Modules.pullback (Spec.map φ)).obj
        ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶
      tilde (ModuleCat.of S ((I.ideal U).map φ.hom)) :=
  (Scheme.Modules.pullback (Spec.map φ)).map
      (idealSheafDataModuleAffineSpecIso I U).hom ≫
    specIdealPullbackImageMap φ (I.ideal U)

theorem affineIdealModulePullbackImageMap_epi (I : X.IdealSheafData)
    [(idealSheafDataModule I).IsQuasicoherent] (U : X.affineOpens)
    {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S) :
    Epi (affineIdealModulePullbackImageMap I U φ) := by
  letI := specIdealPullbackImageMap_epi φ (I.ideal U)
  unfold affineIdealModulePullbackImageMap
  infer_instance

/-- The nonflat factorization now applies to the actual canonical ideal
module of an arbitrary scheme, restricted to its affine chart. -/
theorem affineIdealModulePullbackImageMap_existsUnique_factor (I : X.IdealSheafData)
    [(idealSheafDataModule I).IsQuasicoherent] (U : X.affineOpens)
    {S : CommRingCat.{u}} (φ : Γ(X, U.1) ⟶ S)
    (hI : I.ideal U ≠ ⊥) (hφ : Function.Injective φ.hom) (N : (Spec S).Modules)
    [NoZeroSMulDivisors S ((moduleSpecΓFunctor (R := S)).obj N)]
    (ψ : (Scheme.Modules.pullback (Spec.map φ)).obj
      ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶ N) :
    ∃! δ : tilde (ModuleCat.of S ((I.ideal U).map φ.hom)) ⟶ N,
      affineIdealModulePullbackImageMap I U φ ≫ δ = ψ := by
  let e := (Scheme.Modules.pullback (Spec.map φ)).mapIso
    (idealSheafDataModuleAffineSpecIso I U)
  obtain ⟨δ, hδ, _⟩ := specIdealPullbackImageMap_existsUnique_factor φ (I.ideal U)
    hI hφ N (e.inv ≫ ψ)
  have hfac : affineIdealModulePullbackImageMap I U φ ≫ δ = ψ := by
    change (e.hom ≫ specIdealPullbackImageMap φ (I.ideal U)) ≫ δ = ψ
    rw [Category.assoc, hδ, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  letI := affineIdealModulePullbackImageMap_epi I U φ
  exact ⟨δ, hfac, fun δ' hδ' ↦
    (cancel_epi (affineIdealModulePullbackImageMap I U φ)).mp (hδ'.trans hfac.symm)⟩

/-- A nonzero ideal on an integral scheme is nonzero on every nonempty
affine chart. This discharges the local nonzero-ideal input from the actual
global image-ideal witness. -/
theorem idealSheafData_affine_ideal_ne_bot [IsIntegral X] (I : X.IdealSheafData)
    (hI : I ≠ ⊥) (U : X.affineOpens) [Nonempty U.1] : I.ideal U ≠ ⊥ := by
  intro hz
  apply integral_genericPoint_notMem_support_of_ideal_ne_bot I hI
  apply (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U)
    (genericPoint_mem U.1)).mpr
  rw [hz]
  simp only [Scheme.mem_zeroLocus_iff, Ideal.mem_bot]
  intro f hf
  subst f
  simp

/-- Actual nonzero ideal data and an actual dominant Cartier direct image
supply both geometric side conditions of the nonflat affine factorization. -/
theorem affineIdealModulePullbackImageMap_existsUnique_factor_to_cartier_direct_image
    [IsIntegral X] (I : X.IdealSheafData) (hI : I ≠ ⊥)
    [(idealSheafDataModule I).IsQuasicoherent] (U : X.affineOpens) [Nonempty U.1]
    {S : CommRingCat.{u}} [IsIntegral (Spec S)] (φ : Γ(X, U.1) ⟶ S)
    (hφ : Function.Injective φ.hom) {T : Scheme.{u}} [IsIntegral T]
    (q : T ⟶ Spec S) [IsDominant q] (E : CartierDivisor T)
    (ψ : (Scheme.Modules.pullback (Spec.map φ)).obj
      ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶
        (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : tilde (ModuleCat.of S ((I.ideal U).map φ.hom)) ⟶
        (Scheme.Modules.pushforward q).obj E.sheaf,
      affineIdealModulePullbackImageMap I U φ ≫ δ = ψ := by
  letI := cartier_direct_image_spec_sections_noZeroSMulDivisors q E
  exact affineIdealModulePullbackImageMap_existsUnique_factor I U φ
    (idealSheafData_affine_ideal_ne_bot I hI U) hφ _ ψ

end MixedFujita
