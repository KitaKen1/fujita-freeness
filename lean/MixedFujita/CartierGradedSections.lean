/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionProducts
public import MixedFujita.CartierSectionPowers

/-!
Graded products of actual sections of the multiples j·J of one Cartier divisor.
The product of sections of j·J and k·J is built directly as an actual section of
(j+k)·J, so no transport between section types is needed. Its rational function
and its local coefficients for the powers of one local equation multiply. It is
linear over the base field in the second factor, and multiplication by a nonzero
section is injective. Taylor maps for the powers of one local equation multiply.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierNsmulProduct_mem_sections (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) :
    (rationalFunctionsEquiv (X := X) ⊤).symm
      (cartierSectionRational (j • J) s * cartierSectionRational (k • J) t) ∈
        ((j + k) • J).sections ⊤ := by
  rw [add_nsmul]
  exact cartierSectionProduct_mem_sections (j • J) (k • J) s t

/-- The product of sections of j·J and k·J, as an actual section of (j+k)·J. -/
noncomputable def cartierNsmulProduct (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) : Γ(((j + k) • J).sheaf, ⊤) :=
  CartierDivisor.sectionMk _ (cartierNsmulProduct_mem_sections J j k s t)

theorem cartierNsmulProduct_rational (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) :
    cartierSectionRational ((j + k) • J) (cartierNsmulProduct J j k s t) =
      cartierSectionRational (j • J) s * cartierSectionRational (k • J) t := by
  simp only [cartierNsmulProduct, cartierSectionRational_apply,
    CartierDivisor.sheafι_app_sectionMk, LinearEquiv.apply_symm_apply]

theorem cartierNsmulProduct_localCoefficient (J : CartierDivisor X) (j k : ℕ)
    (x : X) (f : X.functionFieldˣ) (hf : J.IsLocalEquationAt x f)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) :
    cartierLocalCoefficient ((j + k) • J) x (f ^ (j + k)) (cartierLocalEquation_pow J x f hf (j + k))
        (cartierNsmulProduct J j k s t) =
      cartierLocalCoefficient (j • J) x (f ^ j) (cartierLocalEquation_pow J x f hf j) s *
        cartierLocalCoefficient (k • J) x (f ^ k) (cartierLocalEquation_pow J x f hf k) t := by
  apply IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  rw [map_mul, cartierLocalCoefficient_image, cartierLocalCoefficient_image,
    cartierLocalCoefficient_image, cartierNsmulProduct_rational]
  push_cast [pow_add]
  ring

theorem cartierNsmulProduct_injective (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) (hs : s ≠ 0) :
    Function.Injective (cartierNsmulProduct J j k s) := by
  intro t₁ t₂ h
  have h' := congrArg (cartierSectionRational ((j + k) • J)) h
  rw [cartierNsmulProduct_rational, cartierNsmulProduct_rational] at h'
  have hs' : cartierSectionRational (j • J) s ≠ 0 :=
    (map_ne_zero_iff _ (cartierSectionRational_injective (j • J))).mpr hs
  exact cartierSectionRational_injective (k • J) (mul_left_cancel₀ hs' h')

section Base

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseLocalScalarTower cartierBaseSectionScalarTower

/-- Multiplication by a fixed section of j·J, as a base-field linear map. -/
noncomputable def cartierNsmulProductLinear (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) : Γ((k • J).sheaf, ⊤) →ₗ[K] Γ(((j + k) • J).sheaf, ⊤) where
  toFun t := cartierNsmulProduct J j k s t
  map_add' t₁ t₂ := by
    apply cartierSectionRational_injective
    rw [map_add, cartierNsmulProduct_rational, cartierNsmulProduct_rational,
      cartierNsmulProduct_rational, map_add, mul_add]
  map_smul' c t := by
    apply cartierSectionRational_injective
    change cartierSectionRational ((j + k) • J)
        (cartierNsmulProduct J j k s ((algebraMap K Γ(X, ⊤) c) • t)) =
      cartierSectionRational ((j + k) • J)
        ((algebraMap K Γ(X, ⊤) c) • cartierNsmulProduct J j k s t)
    rw [cartierNsmulProduct_rational, map_smul, map_smul, cartierNsmulProduct_rational,
      mul_smul_comm]

theorem cartierNsmulProductLinear_apply (J : CartierDivisor X) (j k : ℕ)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) :
    cartierNsmulProductLinear (K := K) J j k s t = cartierNsmulProduct J j k s t := rfl

theorem cartierTaylorCoordinates_nsmulProduct {n : ℕ} (J : CartierDivisor X) (j k : ℕ)
    (x : X) (f : X.functionFieldˣ) (hf : J.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (s : Γ((j • J).sheaf, ⊤)) (t : Γ((k • J).sheaf, ⊤)) :
    cartierTaylorCoordinates ((j + k) • J) x (f ^ (j + k))
        (cartierLocalEquation_pow J x f hf (j + k)) coordinates (cartierNsmulProduct J j k s t) =
      cartierTaylorCoordinates (j • J) x (f ^ j) (cartierLocalEquation_pow J x f hf j)
          coordinates s *
        cartierTaylorCoordinates (k • J) x (f ^ k) (cartierLocalEquation_pow J x f hf k)
          coordinates t := by
  rw [cartierTaylorCoordinates_apply, cartierNsmulProduct_localCoefficient J j k x f hf,
    map_mul, map_mul, cartierTaylorCoordinates_apply, cartierTaylorCoordinates_apply]

end Base

end MixedFujita
