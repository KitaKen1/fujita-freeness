/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IdealSheafComapModuleEpimorphism
public import Mathlib.RingTheory.Noetherian.Orzech

/-! Compare the genuine global ideal-comap epimorphism with the affine
tensor epimorphism. A surjective endomorphism of the Noetherian affine ideal
module is invertible, so no explicit comparison of five adjunction units is
needed. The actual canonical comparison is retained throughout. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem moduleAffineTopIso_naturality {B : Scheme.{u}} {M N : B.Modules}
    (f : M ⟶ N) (V : B.affineOpens) (s : Γ(M.restrict V.2.fromSpec, ⊤)) :
    (moduleAffineTopIso N V).hom
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor V.2.fromSpec).map f) ⊤ s) =
      Scheme.Modules.Hom.app f V.1 ((moduleAffineTopIso M V).hom s) := by
  change N.presheaf.map (eqToHom (affineFromSpec_image_top V).symm).op
    (Scheme.Modules.Hom.app f (V.2.fromSpec ''ᵁ ⊤) s) =
      Scheme.Modules.Hom.app f V.1
        (M.presheaf.map (eqToHom (affineFromSpec_image_top V).symm).op s)
  exact (f.mapPresheaf.naturality_apply (eqToHom (affineFromSpec_image_top V).symm).op s).symm

theorem moduleRestrict_affine_top_app_surjective {B : Scheme.{u}} {M N : B.Modules}
    (f : M ⟶ N) (V : B.affineOpens)
    (hf : Function.Surjective (Scheme.Modules.Hom.app f V.1)) :
    Function.Surjective
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor V.2.fromSpec).map f) ⊤) := by
  intro t
  obtain ⟨s, hs⟩ := hf ((moduleAffineTopIso N V).hom t)
  refine ⟨(moduleAffineTopIso M V).inv s, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (moduleAffineTopIso N V).hom).1
  rw [moduleAffineTopIso_naturality, Iso.inv_hom_id_apply, hs]

theorem quasicoherentSpec_endomorphism_isIso_of_noetherian_surjective_sections
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    [IsNoetherian R ((moduleSpecΓFunctor (R := R)).obj M)] (f : M ⟶ M)
    (hf : Function.Surjective ((moduleSpecΓFunctor (R := R)).map f).hom) : IsIso f := by
  let G := moduleSpecΓFunctor (R := R)
  letI : IsIso (G.map f) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (IsNoetherian.bijective_of_surjective_endomorphism (G.map f).hom hf)
  let ε := (tilde.adjunction (R := R)).counit
  letI : IsIso (ε.app M) := inferInstanceAs (IsIso M.fromTildeΓ)
  have hfac : (tilde.functor R).map (G.map f) ≫ ε.app M = ε.app M ≫ f :=
    ε.naturality f
  haveI : IsIso (ε.app M ≫ f) := by
    rw [← hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left (ε.app M) f

noncomputable def idealAffineSpecSectionsEquiv {B : Scheme.{u}}
    (I : B.IdealSheafData) (V : B.affineOpens) :
    ((idealSheafDataModule I).restrict V.2.fromSpec).ΓSpec ≃ₗ[Γ(B, V.1)] I.ideal V :=
  (moduleAffineSectionsLinearEquiv (idealSheafDataModule I) V).trans
    (idealSheafDataModuleAffineSectionsEquiv I V)

theorem idealAffineSpecSections_noZeroSMulDivisors {B : Scheme.{u}} [IsIntegral B]
    (I : B.IdealSheafData) (V : B.affineOpens) [Nonempty V.1] :
    NoZeroSMulDivisors Γ(B, V.1)
      ((moduleSpecΓFunctor (R := Γ(B, V.1))).obj
        ((idealSheafDataModule I).restrict V.2.fromSpec)) := by
  letI : NoZeroSMulDivisors Γ(B, V.1) (I.ideal V) :=
    Function.Injective.noZeroSMulDivisors (I.ideal V).subtype
      (I.ideal V).injective_subtype rfl (fun _ _ ↦ rfl)
  let e := idealAffineSpecSectionsEquiv I V
  exact Function.Injective.noZeroSMulDivisors e e.injective e.map_zero
    (fun r s ↦ e.map_smul r s)

theorem actualAffineIdealComapImageMap_existsUnique_factor {B B' : Scheme.{u}}
    (I : B.IdealSheafData) (β : B' ⟶ B)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) (hVU : V.1 ≤ β ⁻¹ᵁ U.1)
    (hI : I.ideal U ≠ ⊥) (hβ : Function.Injective (β.appLE U.1 V.1 hVU).hom)
    (N : (Spec Γ(B', V.1)).Modules)
    [NoZeroSMulDivisors Γ(B', V.1) ((moduleSpecΓFunctor (R := Γ(B', V.1))).obj N)]
    (ψ : (Scheme.Modules.pullback (Spec.map (β.appLE U.1 V.1 hVU))).obj
      ((idealSheafDataModule I).restrict U.2.fromSpec) ⟶ N) :
    ∃! δ : (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec ⟶ N,
      actualAffineIdealComapImageMap I β U V hVU ≫ δ = ψ := by
  let e := affineIdealComapSpecIso I β U V hVU
  obtain ⟨δ, hδ, _⟩ := affineIdealModulePullbackImageMap_existsUnique_factor I U
    (β.appLE U.1 V.1 hVU) hI hβ N ψ
  have hfac : actualAffineIdealComapImageMap I β U V hVU ≫ (e.inv ≫ δ) = ψ := by
    change (affineIdealModulePullbackImageMap I U (β.appLE U.1 V.1 hVU) ≫ e.hom) ≫
      (e.inv ≫ δ) = ψ
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hδ
  letI := actualAffineIdealComapImageMap_epi I β U V hVU
  exact ⟨e.inv ≫ δ, hfac, fun δ' hδ' ↦
    (cancel_epi (actualAffineIdealComapImageMap I β U V hVU)).mp (hδ'.trans hfac.symm)⟩

/-- The actual canonical global comparison has the same factorization
property on affine charts as the tensor comparison. Hopficity replaces an
explicit calculation of the composite chart-adjunction isomorphism. -/
theorem canonicalIdealComapModuleMap_affine_existsUnique_factor
    {B B' : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsLocallyNoetherian B']
    (I : B.IdealSheafData) (hI : I ≠ ⊥) (β : B' ⟶ B) [IsDominant β]
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (U : B.affineOpens) (V : B'.affineOpens) [Nonempty V.1]
    (hVU : V.1 ≤ β ⁻¹ᵁ U.1) (N : (Spec Γ(B', V.1)).Modules)
    [NoZeroSMulDivisors Γ(B', V.1) ((moduleSpecΓFunctor (R := Γ(B', V.1))).obj N)]
    (ψ : (((Scheme.Modules.pullback β).obj (idealSheafDataModule I)).restrict V.2.fromSpec) ⟶ N) :
    ∃! δ : (idealSheafDataModule (I.comap β)).restrict V.2.fromSpec ⟶ N,
      (Scheme.Modules.restrictFunctor V.2.fromSpec).map (idealSheafComapModuleMap I β) ≫ δ = ψ := by
  letI : Nonempty U.1 := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V.1)
    exact ⟨⟨β v.1, hVU v.property⟩⟩
  let J := idealSheafDataModule (I.comap β)
  let Jv := J.restrict V.2.fromSpec
  let G := moduleSpecΓFunctor (R := Γ(B', V.1))
  let e := affineChartPullbackRestrictionIso β (idealSheafDataModule I) U V hVU
  let π := actualAffineIdealComapImageMap I β U V hVU
  let f := (Scheme.Modules.restrictFunctor V.2.fromSpec).map (idealSheafComapModuleMap I β)
  let κ := e.hom ≫ f
  have hlocalI := idealSheafData_affine_ideal_ne_bot I hI U
  have hβ := dominant_affine_chart_coefficients_injective β U V hVU
  letI := idealAffineSpecSections_noZeroSMulDivisors (I.comap β) V
  obtain ⟨γ, hγ, _⟩ := actualAffineIdealComapImageMap_existsUnique_factor I β U V hVU
    hlocalI hβ Jv κ
  have hκ : Function.Surjective (Scheme.Modules.Hom.app κ ⊤) := by
    have hf := moduleRestrict_affine_top_app_surjective (idealSheafComapModuleMap I β) V
      (idealSheafComapModuleMap_affine_app_surjective I β U V hVU)
    have he := (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom ⊤)).2
    exact hf.comp he
  have hγsurj : Function.Surjective (G.map γ).hom := by
    intro t
    obtain ⟨s, hs⟩ := hκ t
    refine ⟨(G.map π).hom s, ?_⟩
    have hh := congrArg (fun z ↦ Scheme.Modules.Hom.app z ⊤ s) hγ
    exact hh.trans hs
  letI : IsNoetherianRing Γ(B', V.1) := IsLocallyNoetherian.component_noetherian V
  letI : IsNoetherian Γ(B', V.1) (G.obj Jv) :=
    isNoetherian_of_linearEquiv (idealAffineSpecSectionsEquiv (I.comap β) V).symm
  letI : Jv.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback V.2.fromSpec).app J).symm
  letI : IsIso γ := quasicoherentSpec_endomorphism_isIso_of_noetherian_surjective_sections Jv γ hγsurj
  obtain ⟨δ, hδ, _⟩ := actualAffineIdealComapImageMap_existsUnique_factor I β U V hVU
    hlocalI hβ N (e.hom ≫ ψ)
  have hfac : f ≫ (inv γ ≫ δ) = ψ := by
    apply (cancel_epi e.hom).mp
    change κ ≫ (inv γ ≫ δ) = e.hom ≫ ψ
    rw [← hγ]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hδ
  letI := actualAffineIdealComapImageMap_epi I β U V hVU
  letI : Epi κ := by
    rw [← hγ]
    infer_instance
  letI : Epi f := epi_of_epi_fac (show e.hom ≫ f = κ from rfl)
  exact ⟨inv γ ≫ δ, hfac, fun δ' hδ' ↦ (cancel_epi f).mp (hδ'.trans hfac.symm)⟩

end MixedFujita
