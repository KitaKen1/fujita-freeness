/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionRatios

/-!
Regular functions from pointwise regularity, and clearing denominators on basic opens (step 4).
On an integral scheme a rational function lying in the local ring of every point of a nonempty
open W is the rational function of an actual section of the structure sheaf over W: it is a
section of the sheaf of the zero Cartier divisor, and the coefficient for the equation 1 is the
regular function. On an affine open U a function on the basic open of f becomes, after
multiplication by a power of f, the restriction of a function on U.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}}

/-- On an affine open, a function on the basic open of f times a power of f extends. -/
theorem affine_basicOpen_section_clear {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    {V : X.Opens} (hVU : V ≤ U) (hV : V = X.basicOpen f) (ξ : Γ(X, V)) :
    ∃ (m : ℕ) (r : Γ(X, U)),
      ξ * X.presheaf.map (homOfLE hVU).op f ^ m = X.presheaf.map (homOfLE hVU).op r := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  have := hU.isLocalization_of_eq_basicOpen f (homOfLE hVU) hV
  exact IsLocalization.Away.surj f ξ

variable [IsIntegral X]

/-- A rational function regular at every point of a nonempty open is a regular function on
it. -/
theorem exists_section_of_forall_mem_stalk_range (W : X.Opens) [Nonempty W]
    (h : X.functionField)
    (hreg : ∀ x ∈ W, h ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ ρ : Γ(X, W), X.germToFunctionField W ρ = h := by
  have hs : (rationalFunctionsEquiv (X := X) W).symm h ∈ (0 : CartierDivisor X).sections W := by
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    refine ⟨1, CartierDivisor.isLocalEquationAt_zero x, ?_⟩
    rw [LinearEquiv.apply_symm_apply, Units.val_one, one_mul]
    exact hreg x hx
  have h0 : rationalUnitClass X W (Additive.ofMul (1 : X.functionFieldˣ)) =
      (0 : CartierDivisor X) |_ W :=
    rationalUnitClass_eq_restrict_of_forall_isLocalEquationAt 0 W 1
      (fun x _ => CartierDivisor.isLocalEquationAt_zero x)
  refine ⟨cartierOpenCoefficient 0 W 1 h0 W le_rfl (CartierDivisor.sectionMk _ hs), ?_⟩
  rw [cartierOpenCoefficient_image, CartierDivisor.sheafι_app_sectionMk,
    LinearEquiv.apply_symm_apply, Units.val_one, one_mul]

end MixedFujita
