/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
Ideal sheaves on affine schemes and their actual Scheme pullbacks.
The formulas preserve the ideals themselves, rather than only their radicals.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory

universe u

theorem affineIdealSheaf_map_top {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (J : X.IdealSheafData) (f : X ⟶ Y) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
  have h : IsAffineOpen (f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa using isAffineOpen_top X
  simpa using Scheme.IdealSheafData.ideal_map J f ⟨⊤, isAffineOpen_top Y⟩ h

theorem affineIdealSheaf_comap {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  have h (J : X.IdealSheafData) :
      (Scheme.IdealSheafData.ofIdealTop I).comap f ≤ J ↔
        I.map f.appTop.hom ≤ J.ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Ideal.map_le_iff_le_comap]
    constructor
    · intro H
      have H' := H ⟨⊤, isAffineOpen_top Y⟩
      simpa [affineIdealSheaf_map_top] using H'
    · intro H
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa [affineIdealSheaf_map_top] using H
  apply le_antisymm
  · exact (h _).mpr (by simp)
  · apply Scheme.IdealSheafData.le_of_isAffine
    simpa using (h _).mp le_rfl

noncomputable def specIdealSheaf {R : Type u} [CommRing R] (I : Ideal R) :
    (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem specIdealSheaf_ideal_top {R : Type u} [CommRing R] (I : Ideal R) :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdealSheaf]

theorem specIdealSheaf_comap {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) :
    (specIdealSheaf I).comap (Spec.map (CommRingCat.ofHom f)) =
      specIdealSheaf (I.map f) := by
  simp only [specIdealSheaf, affineIdealSheaf_comap, Ideal.map_map]
  apply congrArg Scheme.IdealSheafData.ofIdealTop
  apply congrArg (fun g => I.map g)
  exact congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

theorem specIdealSheaf_injective (R : Type u) [CommRing R] :
    Function.Injective (specIdealSheaf (R := R)) := by
  intro I J h
  have h' := congrArg (fun L => L.ideal ⟨⊤, isAffineOpen_top _⟩) h
  rw [specIdealSheaf_ideal_top, specIdealSheaf_ideal_top] at h'
  have h'' := congrArg (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom) h'
  have hc : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = RingHom.id R :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id
  simpa only [Ideal.map_map, hc, Ideal.map_id] using h''

noncomputable def idealSheafSubschemeCongr {X : Scheme.{u}}
    (I J : X.IdealSheafData) (h : I = J) : I.subscheme ≅ J.subscheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme h)

theorem idealSheafSubschemeCongr_hom_ι {X : Scheme.{u}}
    (I J : X.IdealSheafData) (h : I = J) :
    (idealSheafSubschemeCongr I J h).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp [idealSheafSubschemeCongr]

noncomputable def idealSheafPullbackIso {X Y : Scheme.{u}}
    (I : Y.IdealSheafData) (f : X ⟶ Y) (J : X.IdealSheafData) (h : I.comap f = J) :
    J.subscheme ≅ CategoryTheory.Limits.pullback f I.subschemeι :=
  idealSheafSubschemeCongr _ _ h.symm ≪≫ I.comapIso f

theorem idealSheafPullbackIso_hom_fst {X Y : Scheme.{u}}
    (I : Y.IdealSheafData) (f : X ⟶ Y) (J : X.IdealSheafData) (h : I.comap f = J) :
    (idealSheafPullbackIso I f J h).hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
      J.subschemeι := by
  simp only [idealSheafPullbackIso, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst, idealSheafSubschemeCongr_hom_ι]

noncomputable def specIdealSheafPullbackIso {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) :
    (specIdealSheaf (I.map f)).subscheme ≅
      CategoryTheory.Limits.pullback (Spec.map (CommRingCat.ofHom f))
        (specIdealSheaf I).subschemeι :=
  (idealSheafSubschemeCongr _ _ (specIdealSheaf_comap I f).symm) ≪≫
    (specIdealSheaf I).comapIso (Spec.map (CommRingCat.ofHom f))

theorem specIdealSheafPullbackIso_hom_fst {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (f : R →+* S) :
    (specIdealSheafPullbackIso I f).hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
      (specIdealSheaf (I.map f)).subschemeι := by
  simp only [specIdealSheafPullbackIso, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst, idealSheafSubschemeCongr_hom_ι]

end MixedFujita
