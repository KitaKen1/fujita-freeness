/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutDimension

/-! 実イデアル層の支持とアフィン素イデアルの同値。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Affine prime membership detects the ACTUAL support of any ideal sheaf. -/
theorem idealSheaf_mem_support_iff_le_affine_prime
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (x : U.1) :
    x.1 ∈ I.support ↔ I.ideal U ≤ (U.2.primeIdealOf x).asIdeal := by
  rw [I.mem_support_iff_of_mem x.2]
  rw [← U.2.fromSpec_primeIdealOf x]
  change U.2.primeIdealOf x ∈ U.2.fromSpec ⁻¹' X.zeroLocus (I.ideal U : Set Γ(X, U.1)) ↔ _
  rw [U.2.fromSpec_preimage_zeroLocus]
  rfl

end MixedFujita
