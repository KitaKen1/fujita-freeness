/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalGenerationFiniteFamily
public import MixedFujita.CartierSectionPowers

/-!
Actual section operations preserve ordinary Cartier global generation. Local
frame independence, section products and powers, and explicit principal-shift
sections provide the proofs on integral schemes, without smoothness or H0
finiteness assumptions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

/-- Ordinary global generation can be tested using any actual local frame. -/
theorem cartierIsGloballyGenerated_iff_local_frames (D : CartierDivisor X) :
    CartierIsGloballyGenerated D ↔ ∀ x : X, ∀ f : X.functionFieldˣ,
      ∀ hf : D.IsLocalEquationAt x f,
        ∃ s : Γ(D.sheaf, ⊤), IsUnit (cartierLocalCoefficient D x f hf s) := by
  constructor
  · intro h x f hf
    obtain ⟨s, hs⟩ := h x
    obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x f
      (Classical.choose (D.exists_isLocalEquationAt x)) hf
      (Classical.choose_spec (D.exists_isLocalEquationAt x))
    exact ⟨s, by rw [hv s]; exact v.isUnit.mul hs⟩
  · intro h x
    exact h x _ (Classical.choose_spec (D.exists_isLocalEquationAt x))

/-- The product of actual generating sections proves global generation of a sum. -/
theorem cartierIsGloballyGenerated_add (D E : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) (hE : CartierIsGloballyGenerated E) :
    CartierIsGloballyGenerated (D + E) := by
  apply (cartierIsGloballyGenerated_iff_local_frames (D + E)).mpr
  intro x f hf
  obtain ⟨a, ha⟩ := D.exists_isLocalEquationAt x
  obtain ⟨b, hb⟩ := E.exists_isLocalEquationAt x
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD x a ha
  obtain ⟨t, ht⟩ := (cartierIsGloballyGenerated_iff_local_frames E).mp hE x b hb
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (D + E) x f (a * b) hf (ha.mul hb)
  refine ⟨cartierSectionProduct D E s t, ?_⟩
  rw [hv, cartierSectionProduct_localCoefficient D E x a b ha hb s t]
  exact v.isUnit.mul (hs.mul ht)

/-- Actual section powers prove global generation of every nonnegative multiple. -/
theorem cartierIsGloballyGenerated_nsmul (D : CartierDivisor X)
    (hD : CartierIsGloballyGenerated D) (k : ℕ) : CartierIsGloballyGenerated (k • D) := by
  apply (cartierIsGloballyGenerated_iff_local_frames (k • D)).mpr
  intro x f hf
  obtain ⟨a, ha⟩ := D.exists_isLocalEquationAt x
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD x a ha
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (k • D) x f (a ^ k) hf
    (cartierLocalEquation_pow D x a ha k)
  refine ⟨cartierSectionPower D s k, ?_⟩
  rw [hv, cartierSectionPower_localCoefficient D x a ha s k]
  exact v.isUnit.mul (hs.pow k)

/-- Explicit multiplication by the inverse rational unit supplies generating
sections after an actual principal Cartier shift. -/
theorem cartierIsGloballyGenerated_principal_shift (D : CartierDivisor X)
    (g : X.functionFieldˣ) (hD : CartierIsGloballyGenerated D) :
    CartierIsGloballyGenerated (D + principalCartierDivisor X g) := by
  intro x
  obtain ⟨a, ha⟩ := D.exists_isLocalEquationAt x
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD x a ha
  let r := Scheme.Modules.Hom.app (rationalFunctionsMul X (g⁻¹ : X.functionFieldˣ)) ⊤
    (Scheme.Modules.Hom.app D.sheafι ⊤ s)
  have hr : r ∈ (D + principalCartierDivisor X g).sections ⊤ := by
    apply (cartierSections_mem_principalShift D g ⊤ r).mpr
    simpa only [r, rationalFunctionsMul_app_rationalFunctionsMul_inv_app] using
      D.sheafι_app_mem ⊤ s
  let t : Γ((D + principalCartierDivisor X g).sheaf, ⊤) := CartierDivisor.sectionMk r hr
  have ht : cartierSectionRational (D + principalCartierDivisor X g) t =
      (g⁻¹ : X.functionFieldˣ) * cartierSectionRational D s := by
    rw [cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk]
    exact rationalFunctionsEquiv_rationalFunctionsMul_app _ _ _
  have hframe := ha.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x g)
  have hcoeff : cartierLocalCoefficient (D + principalCartierDivisor X g) x (a * g) hframe t =
      cartierLocalCoefficient D x a ha s := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image, ht, Units.val_mul]
    simp [mul_assoc, Units.val_inv_eq_inv_val, g.ne_zero]
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (D + principalCartierDivisor X g) x
    (Classical.choose ((D + principalCartierDivisor X g).exists_isLocalEquationAt x))
    (a * g) (Classical.choose_spec ((D + principalCartierDivisor X g).exists_isLocalEquationAt x)) hframe
  exact ⟨t, by rw [hv t, hcoeff]; exact v.isUnit.mul hs⟩

/-- Global generation depends only on the actual Cartier linear equivalence class. -/
theorem cartierIsGloballyGenerated_principal_shift_iff (D : CartierDivisor X)
    (g : X.functionFieldˣ) :
    CartierIsGloballyGenerated (D + principalCartierDivisor X g) ↔ CartierIsGloballyGenerated D := by
  constructor
  · intro h
    have h' := cartierIsGloballyGenerated_principal_shift
      (D + principalCartierDivisor X g) g⁻¹ h
    have heq : D + principalCartierDivisor X g + principalCartierDivisor X g⁻¹ = D := by
      rw [add_assoc, ← principalCartierDivisor_mul, mul_inv_cancel, principalCartierDivisor_one,
        add_zero]
    simpa only [heq] using h'
  · exact cartierIsGloballyGenerated_principal_shift D g

end MixedFujita
