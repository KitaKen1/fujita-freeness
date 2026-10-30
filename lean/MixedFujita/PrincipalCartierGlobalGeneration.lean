/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.MixedFujitaStatement

/-! Principal Cartier divisors and the zero Cartier divisor are
globally generated on every integral scheme, by the actual inverse
rational-unit section. No ample divisor or nonzero section is supplied. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [IsIntegral X]

theorem principalCartierDivisor_globallyGenerated (f : X.functionFieldˣ) :
    CartierIsGloballyGenerated (principalCartierDivisor X f) := by
  apply (cartierIsGloballyGenerated_iff_local_frames _).mpr
  intro x g hg
  have hf := CartierDivisor.isLocalEquationAt_principalCartierDivisor x f
  obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame (principalCartierDivisor X f) x g f hg hf
  refine ⟨principalUnitSection f, ?_⟩
  rw [hv, principalUnitSection_localCoefficient, mul_one]
  exact v.isUnit

theorem zeroCartierDivisor_globallyGenerated : CartierIsGloballyGenerated (0 : CartierDivisor X) := by
  simpa only [principalCartierDivisor_one] using principalCartierDivisor_globallyGenerated (1 : X.functionFieldˣ)

end MixedFujita
