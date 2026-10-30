/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCartierBaseNeighborhoodSections

/-!
An actual rational unit is a section of a Cartier sheaf exactly when the
distinguished rational unit is a section after adding its principal divisor.
The statement uses actual module morphisms and works on every open, including
the empty open; no normality or Noetherian hypothesis is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Translate actual nonzero rational sections to actual unit sections by
adding the principal divisor, on an arbitrary actual open. -/
theorem cartier_rational_unit_mem_sections_iff_unit_of_add_principal
    {X : Scheme.{u}} [IsIntegral X] (E : CartierDivisor X)
    (u : X.functionFieldˣ) (U : X.Opens) :
    Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X (u : X.functionField)) U
      (Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U))) ∈ E.sections U ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U)) ∈
        (E + principalCartierDivisor X u).sections U := by
  constructor
  · intro h
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf⟩ := E.exists_isLocalEquationAt x
    have hreg := (CartierDivisor.mem_sections.mp h) x hx f hf
    refine ⟨f * u, hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x u), ?_⟩
    simpa only [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one, Units.val_mul]
      using hreg
  · intro h
    apply CartierDivisor.mem_sections.mpr
    intro x hx f hf
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    have hreg := (CartierDivisor.mem_sections.mp h) x hx (f * u)
      (hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x u))
    simpa only [Scheme.rationalFunctionsEquiv_rationalFunctionsMul_app,
      Scheme.rationalFunctionsEquiv_toRationalFunctions_app, map_one, mul_one, Units.val_mul]
      using hreg

end MixedFujita
