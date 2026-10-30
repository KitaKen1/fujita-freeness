/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.AlgebraicGeometry.Noetherian

/-! 全随伴素点回避から実affine係数の非零因子性。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000


/-- On a noetherian affine open, avoiding ALL associated primes,
including embedded ones, makes the actual regular function a nonzerodivisor. -/
theorem affine_function_regular_of_associated_point_unit
    {X : Scheme.{u}} [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U)
    (c : Γ(X, U))
    (h : ∀ (P : Ideal Γ(X, U)) (hP : P ∈ associatedPrimes Γ(X, U) Γ(X, U)),
      hU.fromSpec (⟨P, hP.isPrime⟩ : PrimeSpectrum Γ(X, U)) ∈ X.basicOpen c) :
    c ∈ nonZeroDivisors Γ(X, U) := by
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  by_contra hc
  have hunion : c ∈ ⋃ P ∈ associatedPrimes Γ(X, U) Γ(X, U), (P : Set Γ(X, U)) := by
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
    exact hc
  obtain ⟨P, hP, hcP⟩ := Set.mem_iUnion₂.mp hunion
  let p : PrimeSpectrum Γ(X, U) := ⟨P, hP.isPrime⟩
  have hpoint : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen c := h P hP
  rw [hU.fromSpec_preimage_basicOpen] at hpoint
  exact hpoint hcP

end MixedFujita
