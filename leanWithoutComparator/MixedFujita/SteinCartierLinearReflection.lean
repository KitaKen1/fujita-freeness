/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinCartierSections
public import MixedFujita.CartierSectionPullbackAvoidance
public import MixedFujita.PrincipalCartierGlobalGeneration
public import MixedFujita.TwistedSectionFamily

/-!
Surjective integral Stein-type maps reflect actual Cartier linear equivalence. Descend the
everywhere generating section of a principal pullback using the proved full section descent,
then reflect nonvanishing at a lift of every target point. The downstairs section gives an
actual principal divisor; its rational unit pulls back to the specified upstairs unit.
No birationality or surjectivity of the function-field map is required. In particular the
Cartier pullback itself is injective, which will compare descended consecutive free multiples.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (g : X ⟶ Y) [IsDominant g]
  (happ : ∀ U : Y.Opens, Function.Surjective (g.app U).hom)
  (hsurj : Function.Surjective g)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

include happ hsurj

/-- A principal Cartier pullback descends together with its specified rational unit. -/
theorem stein_cartier_principal_descent (D : CartierDivisor Y) (φ : X.functionFieldˣ)
    (hD : cartierPullback g D = principalCartierDivisor X φ) :
    ∃ ψ : Y.functionFieldˣ, D = principalCartierDivisor Y ψ ∧
      Units.map (dominantFunctionFieldMap g).hom.toMonoidHom ψ = φ := by
  let s := cartierSectionCast hD.symm (principalUnitSection φ)
  have hs (x : X) : x ∈ cartierSectionNonvanishingOpen (cartierPullback g D) s := by
    rw [show s = cartierSectionCast hD.symm (principalUnitSection φ) from rfl,
      cartierSectionNonvanishingOpen_cast]
    apply (mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ x φ
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor x φ)).mpr
    rw [principalUnitSection_localCoefficient]
    exact isUnit_one
  obtain ⟨a, ha⟩ := cartierDominantPullbackSection_surjective_of_open_app_surjective g happ D s
  have haV (y : Y) : y ∈ cartierSectionNonvanishingOpen D a := by
    obtain ⟨x, rfl⟩ := hsurj y
    apply (cartierDominantPullbackSection_nonvanishing_iff g D a x).mp
    rw [ha]
    exact hs x
  have ha0 : a ≠ 0 :=
    (cartierSectionNonvanishingOpen_nonempty_iff D a).mp ⟨⟨genericPoint Y, haV _⟩⟩
  let ψ := (cartierSectionUnit D a ha0)⁻¹
  refine ⟨ψ, ?_, ?_⟩
  · apply cartierDivisor_eq_of_isLocalEquationAt
    intro y
    exact ⟨ψ, isLocalEquationAt_inv_cartierSectionUnit D a ha0 y (haV y),
      CartierDivisor.isLocalEquationAt_principalCartierDivisor y ψ⟩
  · have hr := cartierDominantPullbackSection_rational g D a
    rw [ha, show s = cartierSectionCast hD.symm (principalUnitSection φ) from rfl,
      cartierSectionCast_rational, principalUnitSection_rational] at hr
    apply Units.ext
    change (dominantFunctionFieldMap g).hom ((cartierSectionRational D a)⁻¹) = (φ : X.functionField)
    rw [map_inv₀, hr.symm, Units.val_inv_eq_inv_val, inv_inv]

/-- Actual Cartier pullback is injective along a surjective Stein-type map. -/
theorem stein_cartierPullback_injective : Function.Injective (cartierPullback g) := by
  intro D E hDE
  have hzero : cartierPullback g (D - E) = principalCartierDivisor X 1 := by
    rw [cartierPullback_sub, hDE, sub_self, principalCartierDivisor_one]
  obtain ⟨ψ, hψ, hmap⟩ := stein_cartier_principal_descent g happ hsurj (D - E) 1 hzero
  have hψ1 : ψ = 1 := by
    apply Units.ext
    apply (dominantFunctionFieldMap g).hom.injective
    exact (congrArg (fun z : X.functionFieldˣ => (z : X.functionField)) hmap).trans (map_one _).symm
  rw [hψ1, principalCartierDivisor_one] at hψ
  exact sub_eq_zero.mp hψ

/-- The specified linear equivalence of Cartier pullbacks descends to the same target. -/
theorem stein_cartier_linear_equivalence_reflection (D E : CartierDivisor Y)
    (φ : X.functionFieldˣ)
    (hDE : cartierPullback g D = cartierPullback g E + principalCartierDivisor X φ) :
    ∃ ψ : Y.functionFieldˣ, D = E + principalCartierDivisor Y ψ ∧
      Units.map (dominantFunctionFieldMap g).hom.toMonoidHom ψ = φ := by
  have hsub : cartierPullback g (D - E) = principalCartierDivisor X φ := by
    rw [cartierPullback_sub, hDE]
    abel
  obtain ⟨ψ, hψ, hmap⟩ := stein_cartier_principal_descent g happ hsurj (D - E) φ hsub
  exact ⟨ψ, by rw [← hψ]; abel, hmap⟩

end MixedFujita
