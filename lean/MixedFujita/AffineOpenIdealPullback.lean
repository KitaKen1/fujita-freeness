/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineIdealSheaves
public import MixedFujita.CartierIdealIdentification

/-!
The actual pullback ideal on the preimage of an affine open is the ring-map
image of the original ideal when the preimage is affine. These are exact
ideals, with no passage to radicals or support sets.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

theorem affineIdealSheaf_comap_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have h : I = Scheme.IdealSheafData.ofIdealTop (I.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp
  conv_lhs => rw [h, affineIdealSheaf_comap]
  simp

theorem idealSheaf_affineOpen_restrict_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top U.1.toScheme U.2⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (idealSheaf_map_eqToHom X I U
    ⟨U.1.ι ''ᵁ ⊤, (@isAffineOpen_top U.1.toScheme U.2).image_of_isOpenImmersion U.1.ι⟩
    U.1.ι_image_top.symm).symm

theorem idealSheaf_comap_affineOpen {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (f : X ⟶ Y) (V : Y.affineOpens) (hU : IsAffineOpen (f ⁻¹ᵁ V.1)) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ V.1, hU⟩ =
      (I.ideal V).map (f.app V.1).hom := by
  let U : X.affineOpens := ⟨f ⁻¹ᵁ V.1, hU⟩
  let : IsAffine U.1.toScheme := hU
  let : IsAffine V.1.toScheme := V.2
  have hcomp : (I.comap f).comap U.1.ι = (I.comap V.1.ι).comap (f ∣_ V.1) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have h := affineIdealSheaf_comap_top (I.comap V.1.ι) (f ∣_ V.1)
  rw [← hcomp, idealSheaf_affineOpen_restrict_top, idealSheaf_affineOpen_restrict_top] at h
  apply_fun Ideal.map U.1.topIso.hom.hom at h
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
    CommRingCat.hom_id, Ideal.map_id] at h
  have hc : V.1.topIso.inv ≫ (f ∣_ V.1).appTop ≫ U.1.topIso.hom = f.app V.1 := by
    rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Opens.topIso_hom]
    have hn := f.naturality (eqToHom V.1.ι_image_top).op
    simp only [← Category.assoc]
    erw [hn]
    simp only [Category.assoc, eqToHom_map,
      eqToHom_op, eqToHom_unop, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [Category.assoc, hc] at h
  exact h

end MixedFujita
