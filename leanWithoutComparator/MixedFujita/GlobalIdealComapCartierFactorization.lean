/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalIdealComapAffineFactorization
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Every actual global map from the pulled nonzero ideal module to a
dominant Cartier direct image factors uniquely through the actual comap
ideal module. The local factors kill the canonical comparison's kernel;
the abelian cokernel universal property supplies a genuine global map.
This is factorization, not a base-change isomorphism or semipositivity. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem moduleHom_affine_app_eq_zero_of_restrict_eq_zero {B : Scheme.{u}} {M N : B.Modules}
    (f : M ⟶ N) (V : B.affineOpens)
    (hf : (Scheme.Modules.restrictFunctor V.2.fromSpec).map f = 0) :
    Scheme.Modules.Hom.app f V.1 = 0 := by
  ext s
  have hz : Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctor V.2.fromSpec).map f) ⊤
        ((moduleAffineTopIso M V).inv s) = 0 := by
    rw [hf]
    rfl
  have he := moduleAffineTopIso_naturality f V ((moduleAffineTopIso M V).inv s)
  rw [hz, map_zero, Iso.inv_hom_id_apply] at he
  exact he.symm

theorem moduleHom_eq_zero_of_local_affine_app_eq_zero {B : Scheme.{u}} {M N : B.Modules}
    (f : M ⟶ N)
    (h : ∀ (W : B.Opens) (x : B), x ∈ W →
      ∃ V : B.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧ Scheme.Modules.Hom.app f V.1 = 0) : f = 0 := by
  classical
  apply moduleHom_ext_affine
  intro W
  ext s
  have hx : ∀ x : W.1,
      ∃ V : B.affineOpens, x.1 ∈ V.1 ∧ V.1 ≤ W.1 ∧ Scheme.Modules.Hom.app f V.1 = 0 :=
    fun x ↦ h W.1 x.1 x.property
  choose V hV hle hz using hx
  let F : TopCat.Sheaf AddCommGrpCat B := (SheafOfModules.toSheaf B.ringCatSheaf).obj N
  have hcover : W.1 ≤ ⨆ x : W.1, (V x).1 := by
    intro x hxW
    exact Opens.mem_iSup.mpr ⟨⟨x, hxW⟩, hV ⟨x, hxW⟩⟩
  apply F.eq_of_locally_eq' (fun x : W.1 ↦ (V x).1) W.1
    (fun x ↦ homOfLE (hle x)) hcover (Scheme.Modules.Hom.app f W.1 s) 0
  intro x
  change N.presheaf.map (homOfLE (hle x)).op (Scheme.Modules.Hom.app f W.1 s) =
    N.presheaf.map (homOfLE (hle x)).op 0
  have he := f.mapPresheaf.naturality_apply (homOfLE (hle x)).op s
  change Scheme.Modules.Hom.app f (V x).1
    (M.presheaf.map (homOfLE (hle x)).op s) =
      N.presheaf.map (homOfLE (hle x)).op (Scheme.Modules.Hom.app f W.1 s) at he
  rw [← he, hz x, map_zero]
  rfl

theorem idealSheafComapModuleMap_kernel_comp_cartier_direct_image_zero
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (ψ : (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) :
    kernel.ι (idealSheafComapModuleMap I β) ≫ ψ = 0 := by
  apply moduleHom_eq_zero_of_local_affine_app_eq_zero
  intro W x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := B.isBasis_affineOpens.exists_subset_of_mem_open
    (show β x ∈ (⊤ : B.Opens) from trivial) (⊤ : B.Opens).isOpen
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVs⟩ := B'.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W ⊓ β ⁻¹ᵁ U from ⟨hx, hxU⟩) (W ⊓ β ⁻¹ᵁ U).isOpen
  let Va : B'.affineOpens := ⟨V, hV⟩
  letI : Nonempty V := ⟨⟨x, hxV⟩⟩
  letI := cartier_direct_image_affine_spec_sections_noZeroSMulDivisors q E Va
  let G := Scheme.Modules.restrictFunctor Va.2.fromSpec
  obtain ⟨δ, hδ, _⟩ := canonicalIdealComapModuleMap_affine_existsUnique_factor I hI β
    ⟨U, hU⟩ Va (hVs.trans inf_le_right) _ (G.map ψ)
  have hz : G.map (kernel.ι (idealSheafComapModuleMap I β) ≫ ψ) = 0 := by
    rw [Functor.map_comp, ← hδ, ← Category.assoc, ← Functor.map_comp,
      kernel.condition, Functor.map_zero, zero_comp]
  exact ⟨Va, hxV, hVs.trans inf_le_left,
    moduleHom_affine_app_eq_zero_of_restrict_eq_zero _ Va hz⟩

/-- The actual comap ideal module receives the genuine global factor of
every comparison into a dominant Cartier direct image. No flatness or
invertibility of the original ideal is assumed. -/
theorem idealSheafComapModuleMap_existsUnique_factor_to_cartier_direct_image
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T)
    [(idealSheafDataModule I).IsQuasicoherent]
    [(idealSheafDataModule (I.comap β)).IsQuasicoherent]
    (ψ : (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : idealSheafDataModule (I.comap β) ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      idealSheafComapModuleMap I β ≫ δ = ψ := by
  letI := idealSheafComapModuleMap_epi I β
  have hz := idealSheafComapModuleMap_kernel_comp_cartier_direct_image_zero I hI β q E ψ
  exact ⟨Abelian.epiDesc (idealSheafComapModuleMap I β) ψ hz,
    Abelian.comp_epiDesc _ _ _, fun δ' hδ' ↦
      (cancel_epi (idealSheafComapModuleMap I β)).mp
        (hδ'.trans (Abelian.comp_epiDesc _ _ _).symm)⟩

/-- The actual effective Cartier principalization identifies its negative
Cartier sheaf with the canonical comap ideal module. -/
noncomputable def principalizedComapIdealModuleIso
    {B B' : Scheme.{u}} [IsIntegral B'] (I : B.IdealSheafData) (β : B' ⟶ B)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    (-P).sheaf ≅ idealSheafDataModule (I.comap β) :=
  effectiveCartierIdealModuleIso P hP ≪≫ eqToIso (congrArg idealSheafDataModule hIP)

noncomputable def principalizedIdealPullbackMap
    {B B' : Scheme.{u}} [IsIntegral B'] (I : B.IdealSheafData) (β : B' ⟶ B)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶ (-P).sheaf :=
  idealSheafComapModuleMap I β ≫ (principalizedComapIdealModuleIso I β P hP hIP).inv

theorem principalizedIdealPullbackMap_epi
    {B B' : Scheme.{u}} [IsIntegral B'] (I : B.IdealSheafData) (β : B' ⟶ B)
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β) :
    Epi (principalizedIdealPullbackMap I β P hP hIP) := by
  letI := idealSheafComapModuleMap_epi I β
  unfold principalizedIdealPullbackMap
  infer_instance

/-- For an actual Cartier principalization, quasi-coherence of the comap
ideal is supplied internally by its actual Cartier sheaf isomorphism. -/
theorem principalizedIdealPullbackMap_existsUnique_factor_to_cartier_direct_image
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T) [(idealSheafDataModule I).IsQuasicoherent]
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (ψ : (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) :
    ∃! δ : (-P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      principalizedIdealPullbackMap I β P hP hIP ≫ δ = ψ := by
  let e := principalizedComapIdealModuleIso I β P hP hIP
  letI := (-P).isInvertible_sheaf
  letI : (idealSheafDataModule (I.comap β)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_of_iso e
  obtain ⟨δ, hδ, _⟩ := idealSheafComapModuleMap_existsUnique_factor_to_cartier_direct_image
    I hI β q E ψ
  have hfac : principalizedIdealPullbackMap I β P hP hIP ≫ (e.hom ≫ δ) = ψ := by
    change (idealSheafComapModuleMap I β ≫ e.inv) ≫ (e.hom ≫ δ) = ψ
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hδ
  letI := principalizedIdealPullbackMap_epi I β P hP hIP
  exact ⟨e.hom ≫ δ, hfac, fun δ' hδ' ↦
    (cancel_epi (principalizedIdealPullbackMap I β P hP hIP)).mp (hδ'.trans hfac.symm)⟩

theorem principalizedIdealPullbackMap_existsUnique_nonzero_factor_to_cartier_direct_image
    {B B' T : Scheme.{u}} [IsIntegral B] [IsIntegral B'] [IsIntegral T]
    [IsLocallyNoetherian B'] (I : B.IdealSheafData) (hI : I ≠ ⊥)
    (β : B' ⟶ B) [IsDominant β] (q : T ⟶ B') [IsDominant q]
    (E : CartierDivisor T) [(idealSheafDataModule I).IsQuasicoherent]
    (P : CartierDivisor B') (hP : P.IsEffective)
    (hIP : effectiveCartierIdealSheaf P hP = I.comap β)
    (ψ : (Scheme.Modules.pullback β).obj (idealSheafDataModule I) ⟶
      (Scheme.Modules.pushforward q).obj E.sheaf) (hψ : ψ ≠ 0) :
    ∃! δ : (-P).sheaf ⟶ (Scheme.Modules.pushforward q).obj E.sheaf,
      principalizedIdealPullbackMap I β P hP hIP ≫ δ = ψ ∧ δ ≠ 0 := by
  obtain ⟨δ, hδ, huniq⟩ :=
    principalizedIdealPullbackMap_existsUnique_factor_to_cartier_direct_image I hI β q E P hP hIP ψ
  refine ⟨δ, ⟨hδ, ?_⟩, fun δ' hδ' ↦ huniq δ' hδ'.1⟩
  intro hz
  apply hψ
  simpa only [hz, comp_zero] using hδ.symm

end MixedFujita
