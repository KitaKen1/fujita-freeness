/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ZeroDimensionalIntegralScheme
public import MixedFujita.PrincipalCartierGlobalGeneration
public import MixedFujita.CartierLocalEquationLocus
public import MixedFujita.CartierSectionRatios

/-! Every actual Cartier divisor on a zero-dimensional integral scheme
is zero, and all of its nonnegative multiples are globally generated.
This proves the zero-dimensional F2 conclusion without any klt,
positivity, Iitaka-dimension or vanishing input. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem cartierDivisor_eq_zero_of_subsingleton [Subsingleton X] (D : CartierDivisor X) : D = 0 := by
  have hlocal (x : X) : D.IsLocalEquationAt x (1 : X.functionFieldˣ) := by
    have hx : x = genericPoint X := Subsingleton.elim _ _
    rw [hx]
    exact cartier_isLocalEquationAt_genericPoint D 1
  have he := rationalUnitClass_eq_restrict_of_forall_isLocalEquationAt D ⊤ 1 (fun x _ => hlocal x)
  rw [TopCat.Presheaf.restrict_self] at he
  exact he.symm.trans (map_zero (rationalUnitClass X ⊤))

theorem zeroDimensional_cartierDivisor_eq_zero
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) : D = 0 := by
  letI := zeroDimensional_integral_subsingleton hdim
  exact cartierDivisor_eq_zero_of_subsingleton D

theorem zeroDimensional_cartier_globallyGenerated
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) : CartierIsGloballyGenerated D := by
  rw [zeroDimensional_cartierDivisor_eq_zero hdim D]
  exact zeroCartierDivisor_globallyGenerated

theorem zeroDimensional_all_cartier_multiples_globallyGenerated
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) (m : ℕ) :
    CartierIsGloballyGenerated (m • D) :=
  zeroDimensional_cartier_globallyGenerated hdim _

end MixedFujita
