/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierRestriction

/-!
Invertibility survives restriction to an actual open subscheme, including
an empty open. Pull back a trivializing cover and transport its isomorphisms
through Mathlib's restriction composition and unit isomorphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

noncomputable def unitIsoRestrictOfUnitIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (W : X.Opens)
    (e : SheafOfModules.unit W.toScheme.ringCatSheaf ≅ M.restrict W.ι) :
    SheafOfModules.unit (j ⁻¹ᵁ W).toScheme.ringCatSheaf ≅
      (M.restrict j).restrict (j ⁻¹ᵁ W).ι :=
  (Scheme.Modules.restrictUnitIso (j ∣_ W)).symm ≪≫
    (Scheme.Modules.restrictFunctor (j ∣_ W)).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (j ∣_ W) W.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι j W)).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (j ⁻¹ᵁ W).ι j).app M

theorem isInvertible_restrict_of_isOpenImmersion
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (hM : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y (M.restrict j) := by
  obtain ⟨ι, W, hW, e⟩ :=
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mp hM
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  refine ⟨ι, fun i => j ⁻¹ᵁ W i, j.iSup_preimage_eq_top hW.iSup_eq_top, ?_⟩
  intro i
  exact ⟨unitIsoRestrictOfUnitIso j M (W i) (e i).some⟩

theorem negativeCartier_restrict_isInvertible
    (X : Scheme.{u}) [IsIntegral X] (D : CartierDivisor X)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y ((-D).sheaf.restrict j) :=
  isInvertible_restrict_of_isOpenImmersion j (-D).sheaf (-D).isInvertible_sheaf

end MixedFujita
