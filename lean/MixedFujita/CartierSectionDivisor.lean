/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective

/-!
Construct the actual effective Cartier zero divisor of a nonzero global
section of O_X(D) on an integral scheme. Its difference from D is the actual
principal Cartier divisor of the section's rational function. Principal
translation preserves the actual module sheaf, through multiplication by
that rational function, on every open including the empty open.
This does not construct a blow-up, its strict transform, or a KV lifting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable def cartierSectionRational (D : CartierDivisor X) :
    Γ(D.sheaf, ⊤) →ₗ[Γ(X, ⊤)] X.functionField :=
  (rationalFunctionsEquiv (X := X) ⊤).toLinearMap.comp (D.sheafι.val.app (op ⊤)).hom

theorem cartierSectionRational_apply (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionRational D s =
      rationalFunctionsEquiv ⊤ (Scheme.Modules.Hom.app D.sheafι ⊤ s) := rfl

theorem cartierSectionRational_injective (D : CartierDivisor X) :
    Function.Injective (cartierSectionRational D) :=
  (rationalFunctionsEquiv (X := X) ⊤).injective.comp (D.sheafι_app_injective ⊤)

noncomputable def cartierSectionUnit (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : X.functionFieldˣ :=
  Units.mk0 (cartierSectionRational D s)
    (fun h => hs (cartierSectionRational_injective D (h.trans (map_zero _).symm)))

theorem cartierSectionUnit_val (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    (cartierSectionUnit D s hs : X.functionField) = cartierSectionRational D s := rfl

noncomputable def cartierSectionZeroDivisor (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : CartierDivisor X :=
  D + principalCartierDivisor X (cartierSectionUnit D s hs)

theorem cartierSectionZeroDivisor_localEquation (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (x : X) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) :
    (cartierSectionZeroDivisor D s hs).IsLocalEquationAt x (f * cartierSectionUnit D s hs) :=
  hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x _)

theorem cartierSectionZeroDivisor_isEffective (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    (cartierSectionZeroDivisor D s hs).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro x
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  refine ⟨f * cartierSectionUnit D s hs,
    cartierSectionZeroDivisor_localEquation D s hs x f hf, ?_⟩
  simpa only [Units.val_mul, cartierSectionUnit_val, cartierSectionRational_apply] using
    (CartierDivisor.mem_sections.mp (D.sheafι_app_mem ⊤ s)) x (Opens.mem_top x) f hf

theorem cartierSectionZeroDivisor_sub (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    cartierSectionZeroDivisor D s hs - D =
      principalCartierDivisor X (cartierSectionUnit D s hs) := by
  simp [cartierSectionZeroDivisor, add_sub_cancel_left]

theorem cartierSections_mem_principalShift (D : CartierDivisor X) (g : X.functionFieldˣ)
    (U : X.Opens) (s : Γ(rationalFunctions X, U)) :
    s ∈ (D + principalCartierDivisor X g).sections U ↔
      Scheme.Modules.Hom.app (rationalFunctionsMul X (g : X.functionField)) U s ∈
        D.sections U := by
  constructor
  · intro hs
    apply CartierDivisor.mem_sections.mpr
    intro x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [rationalFunctionsEquiv_rationalFunctionsMul_app, ← mul_assoc]
    exact (CartierDivisor.mem_sections.mp hs) x hx (f * g)
      (hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x g))
  · intro hs
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
    refine ⟨f * g, hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x g), ?_⟩
    simpa only [Units.val_mul, rationalFunctionsEquiv_rationalFunctionsMul_app, mul_assoc] using
      (CartierDivisor.mem_sections.mp hs) x hx f hf

noncomputable def cartierSheafPrincipalShiftHom (D : CartierDivisor X) (g : X.functionFieldˣ) :
    (D + principalCartierDivisor X g).sheaf ⟶ D.sheaf :=
  D.sheafLift ((D + principalCartierDivisor X g).sheafι ≫
    rationalFunctionsMul X (g : X.functionField)) (by
      intro U s
      exact (cartierSections_mem_principalShift D g U _).mp
        ((D + principalCartierDivisor X g).sheafι_app_mem U s))

theorem cartierSheafPrincipalShiftHom_isIso (D : CartierDivisor X) (g : X.functionFieldˣ) :
    IsIso (cartierSheafPrincipalShiftHom D g) := by
  apply D.isIso_sheafLift
  · intro U a b h
    apply (D + principalCartierDivisor X g).sheafι_app_injective U
    exact (Function.LeftInverse.injective
      (rationalFunctionsMul_inv_app_rationalFunctionsMul_app g U)) h
  · intro U s hs
    let t := Scheme.Modules.Hom.app (rationalFunctionsMul X (g⁻¹ : X.functionFieldˣ)) U s
    have ht : t ∈ (D + principalCartierDivisor X g).sections U := by
      apply (cartierSections_mem_principalShift D g U t).mpr
      simpa only [t, rationalFunctionsMul_app_rationalFunctionsMul_inv_app] using hs
    refine ⟨CartierDivisor.sectionMk t ht, ?_⟩
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      CartierDivisor.sheafι_app_sectionMk]
    exact rationalFunctionsMul_app_rationalFunctionsMul_inv_app g U s

noncomputable def cartierSheafPrincipalShiftIso (D : CartierDivisor X) (g : X.functionFieldˣ) :
    (D + principalCartierDivisor X g).sheaf ≅ D.sheaf := by
  let _ := cartierSheafPrincipalShiftHom_isIso D g
  exact asIso (cartierSheafPrincipalShiftHom D g)

end MixedFujita
