/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineIdealSheaves

/-!
Finite compatible ideal-sheaf data on quasi-compact open immersions.
The global candidate is the intersection of the direct images. Open
base change and preservation of finite intersections prove its exact
restriction formula; no ideal-sheaf existence axiom is used.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

open AlgebraicGeometry CategoryTheory Limits

universe u

theorem openIdealSheaf_comap_inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (I J : Y.IdealSheafData) :
    (I ⊓ J).comap f = I.comap f ⊓ J.comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, Ideal.comap_inf]

theorem openIdealSheaf_comap_iInf {X Y : Scheme.{u}} {ι : Type*} [Finite ι]
    (f : X ⟶ Y) [IsOpenImmersion f] (I : ι → Y.IdealSheafData) :
    (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_iInf, iInf_apply, Ideal.comap_iInf]

theorem openPullback_kernel {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [QuasiCompact f] (H : IsPullback f' iU iV f) :
    f.ker.comap iV = f'.ker := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H W).symm

theorem openIdealSheaf_map_baseChange {X Y Z : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] [IsOpenImmersion g]
    (I : X.IdealSheafData) :
    (I.map f).comap g =
      (I.comap (pullback.snd g f)).map (pullback.fst g f) := by
  let J := I.comap (pullback.snd g f)
  let t := Scheme.IdealSheafData.subschemeMap J I (pullback.snd g f)
    (I.le_map_comap (pullback.snd g f))
  have h₁ : IsPullback J.subschemeι t (pullback.snd g f) I.subschemeι :=
    isPullback_of_isClosedImmersion J.subschemeι I.subschemeι t (pullback.snd g f)
      (by simp [t]) (by simp [J])
  have h₂ := h₁.paste_horiz (IsPullback.of_hasPullback g f)
  change (I.subschemeι ≫ f).ker.comap g = (J.subschemeι ≫ pullback.fst g f).ker
  exact openPullback_kernel _ _ _ _ h₂

noncomputable def finiteOpenIdealGlue {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X) (I : ∀ i, (U i).IdealSheafData) :
    X.IdealSheafData := ⨅ i, (I i).map (f i)

theorem finiteOpenIdealGlue_restrict {X : Scheme.{u}} {ι : Type*} [Finite ι]
    (U : ι → Scheme.{u}) (f : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (f i)] [∀ i, QuasiCompact (f i)]
    (I : ∀ i, (U i).IdealSheafData)
    (h : ∀ i j, (I i).comap (pullback.snd (f j) (f i)) =
      (I j).comap (pullback.fst (f j) (f i))) (j : ι) :
    (finiteOpenIdealGlue U f I).comap (f j) = I j := by
  rw [finiteOpenIdealGlue, openIdealSheaf_comap_iInf]
  apply le_antisymm
  · exact (iInf_le _ j).trans (Scheme.IdealSheafData.comap_map_le (I j) (f j))
  · apply le_iInf
    intro i
    rw [openIdealSheaf_map_baseChange, h i j]
    exact Scheme.IdealSheafData.le_map_comap (I j) _

theorem idealSheaf_ideal_eq_of_affine_restriction {X : Scheme.{u}}
    (I J : X.IdealSheafData) (U : X.affineOpens)
    (h : I.comap U.1.ι = J.comap U.1.ι) : I.ideal U = J.ideal U := by
  have : IsAffine U.1.toScheme := U.2
  have h₀ := congrArg (fun L => L.ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩) h
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h₀
  have h₁ := Ideal.comap_injective_of_surjective
    (U.1.ι.appIso ⊤).inv.hom
    (ConcreteCategory.bijective_of_isIso
      (U.1.ι.appIso ⊤).inv).2 h₀
  have hU : (⟨U.1.ι ''ᵁ ⊤,
      (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩ : X.affineOpens) = U :=
    Subtype.ext (Scheme.Opens.ι_image_top U.1)
  exact hU ▸ h₁

theorem idealSheaf_ext_of_affine_restrictions {X : Scheme.{u}} {ι : Type*}
    (I J : X.IdealSheafData) (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (h : ∀ i, I.comap (U i).1.ι = J.comap (U i).1.ι) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
    (fun i => idealSheaf_ideal_eq_of_affine_restriction I J (U i) (h i))

end MixedFujita
