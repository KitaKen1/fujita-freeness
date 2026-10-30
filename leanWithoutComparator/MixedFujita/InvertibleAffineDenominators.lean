/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.InvertibleOpenRestriction
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-!
Actual quasicoherent modules on affine spectra clear denominators on basic
opens. Actual affine-chart restriction identifies these sections with the
ambient module sections. These are ingredients for constructing the actual
ideal data of a general effective Cartier divisor, not an asserted Bertini
or uniform degree theorem.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem quasicoherentSpec_clear_denominator {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R)
    (s : Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, ⊤)),
      M.presheaf.map (homOfLE le_top).op t = f ^ n • s := by
  have h := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen f
  have : IsLocalizedModule.Away f
      ((modulesSpecToSheaf.obj M).obj.map V.leTop.op).hom := h f
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    ((modulesSpecToSheaf.obj M).obj.map V.leTop.op).hom f
      (show ((modulesSpecToSheaf.obj M).obj.obj (op V)) from s)
  exact ⟨n, t, ht.symm⟩

variable {X : Scheme.{u}}

theorem affineFromSpec_image_top (U : X.affineOpens) :
    U.2.fromSpec ''ᵁ ⊤ = U.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]

noncomputable def moduleAffineTopIso (M : X.Modules) (U : X.affineOpens) :
    Γ(M.restrict U.2.fromSpec, ⊤) ≅ Γ(M, U.1) :=
  M.restrictAppIso U.2.fromSpec ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (affineFromSpec_image_top U).symm).op

noncomputable def moduleAffineBasicOpenIso
    (M : X.Modules) (U : X.affineOpens) (f : Γ(X, U.1)) :
    Γ(M.restrict U.2.fromSpec, PrimeSpectrum.basicOpen f) ≅ Γ(M, X.basicOpen f) :=
  M.restrictAppIso U.2.fromSpec (PrimeSpectrum.basicOpen f) ≪≫
    M.presheaf.mapIso (eqToIso (U.2.fromSpec_image_basicOpen f).symm).op

theorem moduleAffineBasicOpenIso_restriction
    (M : X.Modules) (U : X.affineOpens) (f : Γ(X, U.1))
    (s : Γ(M.restrict U.2.fromSpec, ⊤)) :
    (moduleAffineBasicOpenIso M U f).hom
      ((M.restrict U.2.fromSpec).presheaf.map (homOfLE le_top).op s) =
    M.presheaf.map (homOfLE (X.basicOpen_le f)).op
      ((moduleAffineTopIso M U).hom s) := by
  simp only [moduleAffineBasicOpenIso, moduleAffineTopIso, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom,
    ConcreteCategory.comp_apply, Scheme.Modules.map_restrictAppIso_hom_apply]
  simp only [← M.presheaf.map_comp_apply, ← op_comp]
  congr 2

theorem affineFromSpec_top_coefficient (U : X.affineOpens) :
    (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (U.2.fromSpec.appIso ⊤).inv =
      X.presheaf.map (eqToHom (affineFromSpec_image_top U)).op := by
  have h : U.2.fromSpec.appLE U.1 ⊤
      (by rw [U.2.fromSpec_preimage_self]) =
      (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    simp only [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [← h, Scheme.Hom.appLE_appIso_inv]
  congr 1

theorem affineFromSpec_basic_coefficient (U : X.affineOpens) (f : Γ(X, U.1)) :
    (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫
      (Spec Γ(X, U.1)).presheaf.map (homOfLE le_top :
        PrimeSpectrum.basicOpen f ⟶ ⊤).op ≫
      (U.2.fromSpec.appIso (PrimeSpectrum.basicOpen f)).inv ≫
      X.presheaf.map (eqToHom (U.2.fromSpec_image_basicOpen f).symm).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op := by
  rw [Scheme.Hom.appIso_inv_naturality_assoc,
    ← Category.assoc, affineFromSpec_top_coefficient]
  simp only [← Functor.map_comp]
  congr 1

theorem moduleAffineBasicOpenIso_smul (M : X.Modules) (U : X.affineOpens)
    (f a : Γ(X, U.1)) (s : Γ(M.restrict U.2.fromSpec, PrimeSpectrum.basicOpen f)) :
    (moduleAffineBasicOpenIso M U f).hom (a • s) =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op a •
        (moduleAffineBasicOpenIso M U f).hom s := by
  rw [Scheme.Modules.smul_Spec_def]
  simp only [moduleAffineBasicOpenIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, ConcreteCategory.comp_apply, Scheme.Modules.smul_restrictAppIso_hom_apply,
    Scheme.Modules.map_smul]
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply]
  exact congrArg (fun r : Γ(X, X.basicOpen f) ↦ r • _)
    (ConcreteCategory.congr_hom (affineFromSpec_basic_coefficient U f) a)

theorem invertibleAffine_clear_denominator (M : X.Modules)
    (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M)
    (U : X.affineOpens) (f : Γ(X, U.1)) (s : Γ(M, X.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, U.1)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op t =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f) ^ n • s := by
  have := isInvertible_restrict_of_isOpenImmersion U.2.fromSpec M hM
  let N := M.restrict U.2.fromSpec
  obtain ⟨n, t, ht⟩ := quasicoherentSpec_clear_denominator N f
    ((moduleAffineBasicOpenIso M U f).inv s)
  refine ⟨n, (moduleAffineTopIso M U).hom t, ?_⟩
  have h := congrArg (moduleAffineBasicOpenIso M U f).hom ht
  rw [moduleAffineBasicOpenIso_restriction, moduleAffineBasicOpenIso_smul,
    map_pow, Iso.inv_hom_id_apply] at h
  exact h

end MixedFujita
