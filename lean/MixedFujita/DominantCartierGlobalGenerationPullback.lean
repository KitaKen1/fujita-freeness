/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.CartierSectionPullbackAvoidance

/-! Pull actual generating Cartier sections back through a dominant morphism.
The local coefficient is the actual stalk map of the source coefficient, so
the chosen generating unit remains a unit. No ampleness or dimension condition
on the pullback divisor is needed. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Actual Cartier global generation is preserved by dominant pullback. -/
theorem cartierIsGloballyGenerated_dominant_pullback
    {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (h : X ⟶ Z) [IsDominant h] (A : CartierDivisor Z)
    (hA : CartierIsGloballyGenerated A) : CartierIsGloballyGenerated (cartierPullback h A) := by
  apply (cartierIsGloballyGenerated_iff_local_frames _).mpr
  intro x a ha
  obtain ⟨b, hb⟩ := A.exists_isLocalEquationAt (h x)
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames A).mp hA (h x) b hb
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (cartierPullback h A) x a
    (Units.map (dominantFunctionFieldMap h).hom.toMonoidHom b) ha
    (cartierPullback_isLocalEquationAt h A x hb)
  refine ⟨cartierDominantPullbackSection h A s, ?_⟩
  rw [hv, cartierDominantPullbackSection_localCoefficient h A s x b hb]
  exact v.isUnit.mul (hs.map (h.stalkMap x).hom)

end MixedFujita
