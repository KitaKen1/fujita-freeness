/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PrincipalizedIdealCoefficients
public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.CartierBirationalZeroDivisors
public import MixedFujita.ExceptionalCartierSections
public import MixedFujita.CartierNefDefinition
public import MixedFujita.KltPairs

/-!
Global generation after principalization (step 12, section 6.2 of the manuscript).

Let ρ : T → X be a dominant morphism of integral schemes, A_i finitely many effective Cartier
divisors of X, and G an effective Cartier divisor of T whose ideal sheaf is the inverse image of
the sum of the ideal sheaves of the A_i. If M is a Cartier divisor of X such that every M - A_i is
globally generated, then ρ*M - G is globally generated, hence nef.

Proof. At a point t of T the divisor G and some ρ*A_i have a common local equation, so the
effective divisor ρ*A_i - G is trivial near t. A section of ρ*(M - A_i) with unit coefficient at
t is a section of ρ*M - G = ρ*(M - A_i) + (ρ*A_i - G) with unit coefficient at t. This is the
global generation of u ρ*L - G used to make ρ*A - Ψ nef and big.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Effective

variable {X : Scheme.{u}} [IsIntegral X]

/-- If the ideal sheaf of an effective Cartier divisor is contained in the ideal sheaf of another
one, their difference is effective. -/
theorem cartier_sub_isEffective_of_effectiveCartierIdealSheaf_le (D₁ D₂ : CartierDivisor X)
    (h₁ : D₁.IsEffective) (h₂ : D₂.IsEffective)
    (hle : effectiveCartierIdealSheaf D₁ h₁ ≤ effectiveCartierIdealSheaf D₂ h₂) :
    (D₁ - D₂).IsEffective := by
  apply CartierDivisor.isEffective_iff_exists.mpr
  intro x
  obtain ⟨U, hxU, hne, b, hb, hEq⟩ := exists_affineOpen_regularEquations_of_isEffective
    (fun o : Bool => bif o then D₁ else D₂)
    (fun o => by
      cases o with
      | false => exact h₂
      | true => exact h₁) x
  have h1U : (effectiveCartierIdealSheaf D₁ h₁).ideal U = Ideal.span {b true} :=
    effectiveCartierIdealSheaf_ideal_eq_span D₁ h₁ U (b true) (hb true) (hEq true)
  have h2U : (effectiveCartierIdealSheaf D₂ h₂).ideal U = Ideal.span {b false} :=
    effectiveCartierIdealSheaf_ideal_eq_span D₂ h₂ U (b false) (hb false) (hEq false)
  have hmem : b true ∈ Ideal.span ({b false} : Set Γ(X, U.1)) := by
    rw [← h2U]
    exact Scheme.IdealSheafData.le_def.mp hle U (by rw [h1U]; exact Ideal.subset_span rfl)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hloc1 : D₁.IsLocalEquationAt x
      (regularEquationRationalUnit X U.1 (b true) (hb true)) :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hEq true) hxU
  have hloc2 : D₂.IsLocalEquationAt x
      (regularEquationRationalUnit X U.1 (b false) (hb false)) :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hEq false) hxU
  have hgF : X.germToFunctionField U.1 (b false) ≠ 0 := fun h =>
    hb false (X.germToFunctionField_injective U.1 (by rw [h, map_zero]))
  refine ⟨regularEquationRationalUnit X U.1 (b true) (hb true) *
    (regularEquationRationalUnit X U.1 (b false) (hb false))⁻¹, ?_,
    X.presheaf.germ U.1 x hxU r, ?_⟩
  · rw [sub_eq_add_neg]
    exact hloc1.mul hloc2.inv
  · rw [X.algebraMap_germ_eq_germToFunctionField hxU r, Units.val_mul,
      Units.val_inv_eq_inv_val, regularEquationRationalUnit_val,
      regularEquationRationalUnit_val, ← hr, map_mul, mul_assoc, mul_inv_cancel₀ hgF, mul_one]

end Effective

section GlobalGeneration

variable {X : Scheme.{u}} [IsIntegral X]

/-- A section of D with unit coefficient at a point is a section of D + E with unit coefficient
at the point, for every effective E which is trivial near the point. -/
theorem exists_isUnit_cartierLocalCoefficient_add_effective (D E : CartierDivisor X)
    (hE : E.IsEffective) (x : X) (hEx : E.IsLocalEquationAt x 1) (f : X.functionFieldˣ)
    (hf : D.IsLocalEquationAt x f) (s : Γ(D.sheaf, ⊤))
    (hs : IsUnit (cartierLocalCoefficient D x f hf s)) :
    ∃ t : Γ((D + E).sheaf, ⊤),
      IsUnit (cartierLocalCoefficient (D + E) x (f * 1) (hf.mul hEx) t) := by
  have hr : Scheme.Modules.Hom.app D.sheafι ⊤ s ∈ (D + E).sections ⊤ := by
    have h := mem_sections_add_effective_on_open D E hE ⊤ (cartierSectionRational D s) (by
      rw [cartierSectionRational_apply, LinearEquiv.symm_apply_apply]
      exact D.sheafι_app_mem ⊤ s)
    rwa [cartierSectionRational_apply, LinearEquiv.symm_apply_apply] at h
  obtain ⟨t, ht_def⟩ : ∃ t : Γ((D + E).sheaf, ⊤), t = CartierDivisor.sectionMk _ hr := ⟨_, rfl⟩
  have ht : cartierSectionRational (D + E) t = cartierSectionRational D s := by
    rw [ht_def, cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk,
      cartierSectionRational_apply]
  refine ⟨t, ?_⟩
  have hcoeff : cartierLocalCoefficient (D + E) x (f * 1) (hf.mul hEx) t =
      cartierLocalCoefficient D x f hf s := by
    apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image, ht, mul_one]
  rw [hcoeff]
  exact hs

/-- A Cartier divisor is globally generated if, for every point, it is the sum of a globally
generated divisor and an effective divisor which is trivial near the point. -/
theorem cartierIsGloballyGenerated_of_forall_exists_add_effective (P : CartierDivisor X)
    (h : ∀ x : X, ∃ D E : CartierDivisor X, P = D + E ∧ CartierIsGloballyGenerated D ∧
      E.IsEffective ∧ E.IsLocalEquationAt x 1) : CartierIsGloballyGenerated P := by
  apply (cartierIsGloballyGenerated_iff_local_frames P).mpr
  intro x f hf
  obtain ⟨D, E, hP, hD, hE, hEx⟩ := h x
  subst hP
  obtain ⟨a, ha⟩ := D.exists_isLocalEquationAt x
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD x a ha
  obtain ⟨t, ht⟩ := exists_isUnit_cartierLocalCoefficient_add_effective D E hE x hEx a ha s hs
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (D + E) x f (a * 1) hf (ha.mul hEx)
  exact ⟨t, by rw [hv t]; exact v.isUnit.mul ht⟩

end GlobalGeneration

section Principalized

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] (ρ : T ⟶ X) [IsDominant ρ]

/-- Global generation after principalization: if the inverse image of the sum of the ideal
sheaves of finitely many effective Cartier divisors A_i is the ideal sheaf of an effective
Cartier divisor G, and every M - A_i is globally generated, then ρ*M - G is globally
generated. -/
theorem cartierIsGloballyGenerated_cartierPullback_sub_of_principalized {ι : Type*} [Finite ι]
    (M : CartierDivisor X) (A : ι → CartierDivisor X) (hA : ∀ i, (A i).IsEffective)
    (hgen : ∀ i, CartierIsGloballyGenerated (M - A i)) (G : CartierDivisor T)
    (hG : G.IsEffective)
    (h : effectiveCartierIdealSheaf G hG =
      (⨆ i, effectiveCartierIdealSheaf (A i) (hA i)).comap ρ) :
    CartierIsGloballyGenerated (cartierPullback ρ M - G) := by
  apply cartierIsGloballyGenerated_of_forall_exists_add_effective
  intro t
  obtain ⟨i, f, hGf, hAf⟩ :=
    exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ A hA G hG h t
  have hle : effectiveCartierIdealSheaf (cartierPullback ρ (A i))
      (cartierPullback_isEffective ρ (A i) (hA i)) ≤ effectiveCartierIdealSheaf G hG := by
    rw [h, effectiveCartierIdealSheaf_cartierPullback ρ (A i) (hA i)]
    exact Scheme.IdealSheafData.comap_mono ρ
      (le_iSup (fun i => effectiveCartierIdealSheaf (A i) (hA i)) i)
  refine ⟨cartierPullback ρ (M - A i), cartierPullback ρ (A i) - G, ?_,
    cartierIsGloballyGenerated_cartierPullback ρ (M - A i) (hgen i),
    cartier_sub_isEffective_of_effectiveCartierIdealSheaf_le _ _
      (cartierPullback_isEffective ρ (A i) (hA i)) hG hle, ?_⟩
  · rw [cartierPullback_sub]
    abel
  · have h1 := hAf.mul hGf.inv
    rw [mul_inv_cancel, ← sub_eq_add_neg] at h1
    exact h1

end Principalized

section Nef

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A globally generated Cartier divisor is nef: on every curve some section does not vanish
identically. -/
theorem cartierIsGloballyGenerated_isNef {D : CartierDivisor Y}
    (hD : CartierIsGloballyGenerated D) : CartierIsNef K D := by
  intro C _ _ _ _ hC φ _
  obtain ⟨z⟩ : Nonempty C := inferInstance
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ z)
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD (φ z) f hf
  exact cartierCurvePullbackDegree_nonneg_of_image_meets_nonvanishingOpen (K := K) hC D φ s
    ⟨z, (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (φ z) f hf).mpr hs⟩

end Nef

end MixedFujita
