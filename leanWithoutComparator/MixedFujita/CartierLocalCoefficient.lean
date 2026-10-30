/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionDivisor
public import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
Construct the local coefficient of an actual global section of O_X(D),
using an actual local equation of D. It is an injective linear map into
the actual local ring; changing the equation multiplies it by a local
unit. For a Noetherian local ring its canonical map to the maximal-ideal
adic completion is injective as well. A power-series coordinate
isomorphism of this completion is not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

@[instance_reducible]
noncomputable def cartierGlobalStalkAlgebra (x : X) :
    Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
  TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, Opens.mem_top x⟩ : (⊤ : X.Opens))

attribute [local instance] cartierGlobalStalkAlgebra

theorem cartierGlobalStalkFunctionFieldTower (x : X) :
    IsScalarTower Γ(X, ⊤) (X.presheaf.stalk x) X.functionField :=
  AlgebraicGeometry.functionField_isScalarTower X ⊤ (⟨x, Opens.mem_top x⟩ : (⊤ : X.Opens))

attribute [local instance] cartierGlobalStalkFunctionFieldTower

noncomputable def cartierStalkToFunctionField (x : X) :
    X.presheaf.stalk x →ₗ[Γ(X, ⊤)] X.functionField :=
  (IsScalarTower.toAlgHom Γ(X, ⊤) (X.presheaf.stalk x) X.functionField).toLinearMap

theorem cartierStalkToFunctionField_injective (x : X) :
    Function.Injective (cartierStalkToFunctionField x) :=
  IsFractionRing.injective (X.presheaf.stalk x) X.functionField

noncomputable def cartierLocalCoefficient (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    Γ(D.sheaf, ⊤) →ₗ[Γ(X, ⊤)] X.presheaf.stalk x :=
  ((LinearEquiv.ofInjective (cartierStalkToFunctionField x)
    (cartierStalkToFunctionField_injective x)).symm.toLinearMap).comp
      (((LinearMap.mulLeft Γ(X, ⊤) (f : X.functionField)).comp
        (cartierSectionRational D)).codRestrict (cartierStalkToFunctionField x).range (by
          intro s
          exact (CartierDivisor.mem_sections.mp (D.sheafι_app_mem ⊤ s)) x
            (Opens.mem_top x) f hf))

theorem cartierLocalCoefficient_image (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) :
    algebraMap (X.presheaf.stalk x) X.functionField (cartierLocalCoefficient D x f hf s) =
      (f : X.functionField) * cartierSectionRational D s := by
  exact LinearEquiv.ofInjective_symm_apply (cartierStalkToFunctionField x)
    (h := cartierStalkToFunctionField_injective x) _

theorem cartierLocalCoefficient_injective (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    Function.Injective (cartierLocalCoefficient D x f hf) := by
  intro s t h
  apply cartierSectionRational_injective D
  apply mul_left_cancel₀ (Units.ne_zero f)
  exact (cartierLocalCoefficient_image D x f hf s).symm.trans
    ((congrArg (algebraMap (X.presheaf.stalk x) X.functionField) h).trans
      (cartierLocalCoefficient_image D x f hf t))

theorem cartierLocalCoefficient_ne_zero_iff (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) : cartierLocalCoefficient D x f hf s ≠ 0 ↔ s ≠ 0 := by
  exact (map_ne_zero_iff _ (cartierLocalCoefficient_injective D x f hf))

theorem cartierLocalCoefficient_change_frame (D : CartierDivisor X)
    (x : X) (f g : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (hg : D.IsLocalEquationAt x g) :
    ∃ v : (X.presheaf.stalk x)ˣ, ∀ s : Γ(D.sheaf, ⊤),
      cartierLocalCoefficient D x f hf s =
        (v : X.presheaf.stalk x) * cartierLocalCoefficient D x g hg s := by
  obtain ⟨v, hv⟩ := hf.exists_unit_mul_eq hg
  refine ⟨v, fun s => ?_⟩
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, cartierLocalCoefficient_image, cartierLocalCoefficient_image, ← mul_assoc, hv]

noncomputable def cartierCompletedLocalCoefficient (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    Γ(D.sheaf, ⊤) →ₗ[Γ(X, ⊤)]
      AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) :=
  ((AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x)).restrictScalars Γ(X, ⊤)).comp (cartierLocalCoefficient D x f hf)

theorem cartierCompletedLocalCoefficient_apply (D : CartierDivisor X)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) :
    cartierCompletedLocalCoefficient D x f hf s =
      AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) (cartierLocalCoefficient D x f hf s) := rfl

theorem cartierCompletedLocalCoefficient_injective (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    Function.Injective (cartierCompletedLocalCoefficient D x f hf) :=
  (AdicCompletion.of_injective (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (X.presheaf.stalk x)).comp (cartierLocalCoefficient_injective D x f hf)

theorem cartierCompletedLocalCoefficient_ne_zero_iff (D : CartierDivisor X)
    (x : X) [IsNoetherianRing (X.presheaf.stalk x)]
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) : cartierCompletedLocalCoefficient D x f hf s ≠ 0 ↔ s ≠ 0 :=
  map_ne_zero_iff _ (cartierCompletedLocalCoefficient_injective D x f hf)

end MixedFujita
