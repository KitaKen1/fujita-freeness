/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.InvertibleIdealPresentation

/-!
The pulled-back closed subscheme on an ambient base-open restriction is
isomorphic, over that base open, to the canonical base-open restriction of
the original closed subscheme. This identifies actual Scheme projections.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X S : Scheme.{u}}

noncomputable def idealSheafOpenBaseRestrictionMap
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens) :
    (I.comap (p ⁻¹ᵁ U).ι).subscheme ⟶ I.subscheme :=
  Scheme.IdealSheafData.subschemeMap (I.comap (p ⁻¹ᵁ U).ι) I (p ⁻¹ᵁ U).ι
    (I.le_map_comap (p ⁻¹ᵁ U).ι)

theorem idealSheafOpenBaseRestriction_isPullback
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens) :
    IsPullback (idealSheafOpenBaseRestrictionMap p I U)
      ((I.comap (p ⁻¹ᵁ U).ι).subschemeι ≫ p ∣_ U) (I.subschemeι ≫ p) U.ι := by
  let J := I.comap (p ⁻¹ᵁ U).ι
  let m := idealSheafOpenBaseRestrictionMap p I U
  have h : IsPullback J.subschemeι m (p ⁻¹ᵁ U).ι I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _
      (by simp [m, J, idealSheafOpenBaseRestrictionMap]) (by simp [J])
  exact h.flip.paste_vert (isPullback_morphismRestrict p U).flip

noncomputable def idealSheafOpenBaseRestrictionIso
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens) :
    (I.comap (p ⁻¹ᵁ U).ι).subscheme ≅
      ((I.subschemeι ≫ p) ⁻¹ᵁ U).toScheme :=
  (idealSheafOpenBaseRestriction_isPullback p I U).isoIsPullback _ _
    (isPullback_morphismRestrict (I.subschemeι ≫ p) U).flip

@[reassoc (attr := simp)]
theorem idealSheafOpenBaseRestrictionIso_hom_projection
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens) :
    (idealSheafOpenBaseRestrictionIso p I U).hom ≫ (I.subschemeι ≫ p) ∣_ U =
      (I.comap (p ⁻¹ᵁ U).ι).subschemeι ≫ p ∣_ U :=
  IsPullback.isoIsPullback_hom_snd _ _ (idealSheafOpenBaseRestriction_isPullback p I U)
    (isPullback_morphismRestrict (I.subschemeι ≫ p) U).flip

@[reassoc (attr := simp)]
theorem idealSheafOpenBaseRestrictionIso_hom_toOriginal
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens) :
    (idealSheafOpenBaseRestrictionIso p I U).hom ≫ ((I.subschemeι ≫ p) ⁻¹ᵁ U).ι =
      idealSheafOpenBaseRestrictionMap p I U :=
  IsPullback.isoIsPullback_hom_fst _ _ (idealSheafOpenBaseRestriction_isPullback p I U)
    (isPullback_morphismRestrict (I.subschemeι ≫ p) U).flip

theorem idealSheafOpenBaseRestriction_property
    (p : X ⟶ S) (I : X.IdealSheafData) (U : S.Opens)
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (h : P ((I.subschemeι ≫ p) ∣_ U)) :
    P ((I.comap (p ⁻¹ᵁ U).ι).subschemeι ≫ p ∣_ U) := by
  rw [← idealSheafOpenBaseRestrictionIso_hom_projection]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr h

end MixedFujita
