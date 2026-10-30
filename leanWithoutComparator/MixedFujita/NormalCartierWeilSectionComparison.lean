/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierRationalUnitSections
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Sheaf

/-! Use the verified normal Hartogs criterion to compare the actual Cartier
and Weil divisor sheaves in every dimension, on all opens and preserving
the actual inclusions into the same rational-function sheaf. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ η : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (η : X))]

/-- Normal Hartogs gives the actual Cartier rational-section criterion in
arbitrary dimension, including the zero rational function. -/
theorem normal_cartier_rational_mem_sections_iff_prime_orders
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) (U : X.Opens) [Nonempty U] (z : X.functionField) :
    (rationalFunctionsEquiv (X := X) U).symm z ∈ D.sections U ↔
      z = 0 ∨ ∀ η : CodimensionOnePoint X, (η : X) ∈ U →
        -cartierCoefficient D (η : X) ≤ X.ord z (η : X) := by
  by_cases hz : z = 0
  · simp only [hz, map_zero, Submodule.zero_mem, true_or]
  rw [or_iff_right hz]
  let u : X.functionFieldˣ := Units.mk0 z hz
  have hrat : Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X (u : X.functionField)) U
      (Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U))) =
      (rationalFunctionsEquiv (X := X) U).symm z := by
    apply (rationalFunctionsEquiv (X := X) U).injective
    rw [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [← hrat, cartier_rational_unit_mem_sections_iff_unit_of_add_principal,
    normal_cartier_one_mem_sections_iff_coefficients_nonneg_on_open hnorm]
  constructor
  · intro h η hηU
    have hc := h η hηU
    rw [cartierCoefficient_add, cartierCoefficient_principal] at hc
    change 0 ≤ cartierCoefficient D (η : X) + X.ord z (η : X) at hc
    omega
  · intro h η hηU
    rw [cartierCoefficient_add, cartierCoefficient_principal]
    change 0 ≤ cartierCoefficient D (η : X) + X.ord z (η : X)
    have hc := h η hηU
    omega

/-- The actual Cartier and Weil rational-section submodules agree on every
open of a normal Noetherian integral scheme, in every dimension. -/
theorem normal_cartier_sections_eq_toWeil_sections
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) (U : X.Opens) :
    D.sections U = SchemeWeilDivisor.sections D.toWeilDivisor U := by
  classical
  by_cases hU : Nonempty U
  · letI := hU
    ext s
    have h := normal_cartier_rational_mem_sections_iff_prime_orders hnorm D U
      (rationalFunctionsEquiv (X := X) U s)
    simpa only [LinearEquiv.symm_apply_apply, SchemeWeilDivisor.mem_sections_iff,
      cartier_toWeilDivisor_coeff_eq_cartierCoefficient] using h
  · have hbot : U = ⊥ := (Opens.not_nonempty_iff_eq_bot U).mp
      (fun ⟨x, hx⟩ => hU ⟨⟨x, hx⟩⟩)
    letI := Scheme.subsingleton_rationalFunctions U hbot
    ext s
    have hs : s = 0 := Subsingleton.elim _ _
    simp only [hs, Submodule.zero_mem]

/-- The actual Cartier sheaf equals the actual associated Weil sheaf on a
normal Noetherian integral scheme, without a dimension-one hypothesis. -/
noncomputable def normalCartierWeilSheafIso
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) : D.sheaf ≅ SchemeWeilDivisor.sheaf D.toWeilDivisor := by
  let φ := D.sheafι
  have hφ (U : X.Opens) (s : Γ(D.sheaf, U)) :
      Scheme.Modules.Hom.app φ U s ∈ SchemeWeilDivisor.sections D.toWeilDivisor U := by
    rw [← normal_cartier_sections_eq_toWeil_sections hnorm]
    exact D.sheafι_app_mem U s
  let f := SchemeWeilDivisor.sheafLift D.toWeilDivisor φ hφ
  have hf : IsIso f := by
    apply SchemeWeilDivisor.isIso_sheafLift D.toWeilDivisor φ hφ
      (D.sheafι_app_injective)
    intro U s hs
    have hm : s ∈ D.sections U := by
      rw [normal_cartier_sections_eq_toWeil_sections hnorm]
      exact hs
    exact ⟨CartierDivisor.sectionMk s hm, CartierDivisor.sheafι_app_sectionMk s hm⟩
  letI := hf
  exact asIso f

/-- The arbitrary-dimensional normal comparison preserves the actual
inclusions into the same rational-function sheaf. -/
theorem normalCartierWeilSheafIso_hom_ι
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D : CartierDivisor X) :
    (normalCartierWeilSheafIso hnorm D).hom ≫ SchemeWeilDivisor.sheafι D.toWeilDivisor =
      D.sheafι := by
  unfold normalCartierWeilSheafIso
  simp only [asIso_hom, SchemeWeilDivisor.sheafLift_ι]

end MixedFujita
