/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierStalkPullbackOrder
public import MixedFujita.ModulePullbackSections

/-!
An actual equation on an open produces an actual isomorphism from the
Cartier module to the structure module on that open. Its coefficient
morphism multiplies the rational section by that equation; its germ is the
previously constructed intrinsic local coefficient. Pulling this regular
coefficient through the actual scheme map gives exactly the actual
restricted Cartier stalk coefficient. No source rational function is
pulled through a function-field map along a possibly nondominant curve.
The local frame pullback/global unit commuting square is constructed in
CartierLocalPullbackFrame. Its components/germs and transition units for a
chosen target Cartier representation still need to be identified.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierOpenFrameIso (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    D.sheaf.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  CartierDivisor.sheafOverIsoOfRestrictEq D (principalCartierDivisor X f) U
    (hf.symm.trans (principalCartierDivisor_restrict X f U).symm) ≪≫
      (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
        (CartierDivisor.unitIsoSheafPrincipalCartierDivisor X f).symm

theorem cartierOpenFrameIso_hom_toRationalFunctions (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U) :
    (cartierOpenFrameIso D U f hf).hom ≫ (toRationalFunctions X).over U =
      D.sheafι.over U ≫ (rationalFunctionsMul X (f : X.functionField)).over U := by
  unfold cartierOpenFrameIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc, ← Functor.map_comp,
    CartierDivisor.unitIsoSheafPrincipalCartierDivisor_inv_toRationalFunctions,
    Functor.map_comp, ← Category.assoc, CartierDivisor.sheafOverIsoOfRestrictEq_hom_ι]

noncomputable def cartierOpenCoefficient (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (W : X.Opens) (hWU : W ≤ U) : Γ(D.sheaf, W) →ₗ[Γ(X, W)] Γ(X, W) :=
  ((cartierOpenFrameIso D U f hf).hom.val.app (op (Over.mk (homOfLE hWU)))).hom

theorem cartierOpenCoefficient_image (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (W : X.Opens) [Nonempty W] (hWU : W ≤ U) (s : Γ(D.sheaf, W)) :
    X.germToFunctionField W (cartierOpenCoefficient D U f hf W hWU s) =
      (f : X.functionField) * rationalFunctionsEquiv W (Scheme.Modules.Hom.app D.sheafι W s) := by
  have h := congrArg (fun c => c.val.app (op (Over.mk (homOfLE hWU))) s)
    (cartierOpenFrameIso_hom_toRationalFunctions D U f hf)
  change Scheme.Modules.Hom.app (toRationalFunctions X) W
    (cartierOpenCoefficient D U f hf W hWU s) =
      Scheme.Modules.Hom.app (rationalFunctionsMul X (f : X.functionField)) W
        (Scheme.Modules.Hom.app D.sheafι W s) at h
  simpa only [rationalFunctionsEquiv_toRationalFunctions_app,
    rationalFunctionsEquiv_rationalFunctionsMul_app] using congrArg (rationalFunctionsEquiv W) h

theorem cartierOpenCoefficient_bijective (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (W : X.Opens) (hWU : W ≤ U) :
    Function.Bijective (cartierOpenCoefficient D U f hf W hWU) :=
  ConcreteCategory.bijective_of_isIso
    ((PresheafOfModules.evaluation _ (op (Over.mk (homOfLE hWU)))).mapIso
      ((SheafOfModules.forget _).mapIso (cartierOpenFrameIso D U f hf))).hom

theorem cartierOpenCoefficient_restrict (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    {W V : X.Opens} (hWU : W ≤ U) (i : V ⟶ W) (s : Γ(D.sheaf, W)) :
    cartierOpenCoefficient D U f hf V (i.le.trans hWU) (D.sheaf.presheaf.map i.op s) =
      X.presheaf.map i.op (cartierOpenCoefficient D U f hf W hWU s) := by
  exact PresheafOfModules.naturality_apply (cartierOpenFrameIso D U f hf).hom.val
    (Over.homMk i : Over.mk (homOfLE (i.le.trans hWU)) ⟶ Over.mk (homOfLE hWU)).op s

theorem cartierOpenCoefficient_germ_global (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (x : X) (hx : x ∈ U) (s : Γ(D.sheaf, ⊤)) :
    X.presheaf.germ U x hx (cartierOpenCoefficient D U f hf U le_rfl
      (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s)) =
        cartierLocalCoefficient D x f (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) s := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [X.algebraMap_germ_eq_germToFunctionField hx, cartierOpenCoefficient_image,
    cartierLocalCoefficient_image, cartierSectionRational_apply]
  congr 1
  have h := ConcreteCategory.congr_hom
    (D.sheafι.mapPresheaf.naturality (homOfLE le_top : U ⟶ ⊤).op) s
  change Scheme.Modules.Hom.app D.sheafι U
    (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) =
      (rationalFunctions X).presheaf.map (homOfLE le_top : U ⟶ ⊤).op
        (Scheme.Modules.Hom.app D.sheafι ⊤ s) at h
  rw [h, rationalFunctionsEquiv_map]

theorem cartierOpenCoefficient_pullback_germ_global (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) :
    Y.presheaf.germ (φ ⁻¹ᵁ U) y hy (φ.app U (cartierOpenCoefficient D U f hf U le_rfl
      (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s))) =
        cartierStalkPullbackCoefficient D φ y f
          (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hy) s := by
  rw [cartierStalkPullbackCoefficient_apply, ← cartierOpenCoefficient_germ_global D U f hf (φ y) hy]
  exact (Scheme.Hom.germ_stalkMap_apply φ U y hy _).symm

theorem cartierOpenCoefficient_ne_zero_iff (D : CartierDivisor X) (U : X.Opens) [Nonempty U]
    (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (x : X) (hx : x ∈ U) (s : Γ(D.sheaf, ⊤)) :
    cartierOpenCoefficient D U f hf U le_rfl
      (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) ≠ 0 ↔ s ≠ 0 := by
  constructor
  · intro h hs
    subst hs
    simp at h
  · intro hs h
    have hzero := congrArg (X.presheaf.germ U x hx) h
    rw [cartierOpenCoefficient_germ_global, map_zero] at hzero
    exact (cartierLocalCoefficient_ne_zero_iff D x f
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hx) s).mpr hs hzero

end MixedFujita
