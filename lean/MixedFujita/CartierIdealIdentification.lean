/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveRegularCartier
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
Affine ideal-sheaf data and the negative Cartier sheaf agree whenever
they have the same regular principal equations on an affine cover.
The comparison is in actual local rings and preserves multiplicities.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable (X : Scheme.{u})

theorem idealSheaf_map_eqToHom (I : X.IdealSheafData)
    (U V : X.affineOpens) (h : U.1 = V.1) :
    (I.ideal U).map (X.presheaf.map (eqToHom h.symm).op).hom = I.ideal V := by
  have hUV : U = V := Subtype.ext h
  subst V
  simp

theorem idealSheaf_germ_image_eq (I : X.IdealSheafData)
    (U V : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hxU).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩) (U.1 ⊓ V.1).isOpen
  have hWU := I.map_ideal (U := ⟨W, hW⟩) (V := U) (hWUV.trans inf_le_left)
  have hWV := I.map_ideal (U := ⟨W, hW⟩) (V := V) (hWUV.trans inf_le_right)
  apply_fun Ideal.map (X.presheaf.germ W x hxW).hom at hWU
  apply_fun Ideal.map (X.presheaf.germ W x hxW).hom at hWV
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, homOfLE_leOfHom,
    TopCat.Presheaf.germ_res'] at hWU hWV
  exact hWU.trans hWV.symm

variable [IsIntegral X]

theorem regularEquation_inverse_mul_mem_stalk_range_iff
    (U W : X.Opens) [Nonempty U] [Nonempty W]
    (f : Γ(X, U)) (hf : f ≠ 0) (s : Γ(X, W))
    (x : X) (hxU : x ∈ U) (hxW : x ∈ W) :
    ((regularEquationRationalUnit X U f hf)⁻¹ : X.functionField) *
        X.germToFunctionField W s ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range ↔
        X.presheaf.germ W x hxW s ∈
          Ideal.span ({X.presheaf.germ U x hxU f} : Set (X.presheaf.stalk x)) := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [map_mul, X.algebraMap_germ_eq_germToFunctionField hxU,
      X.algebraMap_germ_eq_germToFunctionField hxW, ha]
    change X.germToFunctionField W s =
      (regularEquationRationalUnit X U f hf : X.functionField) *
        (((regularEquationRationalUnit X U f hf)⁻¹ : X.functionField) *
          X.germToFunctionField W s)
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have hm := congrArg (algebraMap (X.presheaf.stalk x) X.functionField) ha
    rw [map_mul, X.algebraMap_germ_eq_germToFunctionField hxU,
      X.algebraMap_germ_eq_germToFunctionField hxW] at hm
    rw [hm]
    change algebraMap (X.presheaf.stalk x) X.functionField a =
      ((regularEquationRationalUnit X U f hf)⁻¹ : X.functionField) *
        ((regularEquationRationalUnit X U f hf : X.functionField) *
          algebraMap (X.presheaf.stalk x) X.functionField a)
    rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]

theorem negativeCartier_regularSection_mem_idealSheaf_iff
    (D : CartierDivisor X) (I : X.IdealSheafData)
    {ι : Type*} (U : ι → X.affineOpens) [∀ i, Nonempty (U i).1]
    (hcover : (⨆ i, (U i).1) = ⊤)
    (f : ∀ i, Γ(X, (U i).1)) (hf : ∀ i, f i ≠ 0)
    (hD : ∀ i, rationalUnitClass X (U i).1
      (Additive.ofMul (regularEquationRationalUnit X (U i).1 (f i) (hf i))) =
        D |_ (U i).1)
    (hI : ∀ i, I.ideal (U i) = Ideal.span ({f i} : Set Γ(X, (U i).1)))
    (W : X.affineOpens) (s : Γ(X, W.1)) :
    Scheme.Modules.Hom.app (toRationalFunctions X) W.1 s ∈ (-D).sections W.1 ↔
      s ∈ I.ideal W := by
  constructor
  · intro hs
    apply W.2.mem_ideal_iff.mpr
    intro x hxW
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    let : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    have hneg := (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hD i) hi).inv
    have hr := CartierDivisor.mem_sections.mp hs x hxW _ hneg
    rw [rationalFunctionsEquiv_toRationalFunctions_app] at hr
    rw [idealSheaf_germ_image_eq X I W (U i) x hxW hi, hI i,
      Ideal.map_span, Set.image_singleton]
    exact (regularEquation_inverse_mul_mem_stalk_range_iff
      X (U i).1 W.1 (f i) (hf i) s x hi hxW).mp hr
  · intro hs
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hxW
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Set.mem_univ x))
    let : Nonempty W.1 := ⟨⟨x, hxW⟩⟩
    refine ⟨(regularEquationRationalUnit X (U i).1 (f i) (hf i))⁻¹,
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hD i) hi).inv, ?_⟩
    rw [rationalFunctionsEquiv_toRationalFunctions_app]
    apply (regularEquation_inverse_mul_mem_stalk_range_iff
      X (U i).1 W.1 (f i) (hf i) s x hi hxW).mpr
    have hg := Ideal.mem_map_of_mem (X.presheaf.germ W.1 x hxW).hom hs
    rw [idealSheaf_germ_image_eq X I W (U i) x hxW hi, hI i,
      Ideal.map_span, Set.image_singleton] at hg
    exact hg

end MixedFujita
