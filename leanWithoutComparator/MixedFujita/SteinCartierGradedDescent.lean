/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinCartierSectionEquiv
public import MixedFujita.LinearEffectiveFreenessStatement

/-!
For an actual Cartier equality D = g*H + div(phi) along an integral Stein-type morphism,
identify the full global sections of every multiple of D with those of the same multiple of H.
The comparison is an actual linear equivalence and preserves Iitaka growth in both directions.
If the morphism is surjective, global generation of each multiple is also equivalent. These
statements use one fixed target and divisor at every degree; no birationality is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

section Graded

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]
  [Y.Over (Spec (CommRingCat.of K))] (g : X ⟶ Y) [IsDominant g]
  [g.IsOver (Spec (CommRingCat.of K))]
  (happ : ∀ U : Y.Opens, Function.Surjective (g.app U).hom)
  (D : CartierDivisor X) (H : CartierDivisor Y) (φ : X.functionFieldˣ)
  (hD : D = cartierPullback g H + principalCartierDivisor X φ)

attribute [local instance] cartierBaseGlobalAlgebra functionFieldBaseAlgebra
  cartierBaseSectionScalarTower functionFieldBaseScalarTower

include K happ hD

/-- An actual linear equivalence in every degree, with the same descended divisor H. -/
noncomputable def steinCartierGradedSectionEquiv (q : ℕ) :
    Γ((q • D).sheaf, ⊤) ≃ₗ[K] Γ((q • H).sheaf, ⊤) := by
  rw [hD, nsmul_add, ← principalCartierDivisor_power, ← cartierPullback_nsmul]
  exact (cartierPrincipalShiftEquiv (K := K) (cartierPullback g (q • H)) (φ ^ q)).trans
    (steinCartierSectionEquiv g K happ (q • H)).symm

/-- Full section dimensions, not just the dimensions of the chosen linear system. -/
theorem stein_finrank_graded_of_eq_pullback_add_principal (q : ℕ) :
    Module.finrank K Γ((q • D).sheaf, ⊤) = Module.finrank K Γ((q • H).sheaf, ⊤) :=
  (steinCartierGradedSectionEquiv K g happ D H φ hD q).finrank_eq

/-- The actual growth definition of Iitaka dimension is invariant under Stein Cartier descent. -/
theorem stein_cartierIitakaDimension_iff_of_eq_pullback_add_principal (k : ℕ) :
    CartierIitakaDimension K D k ↔ CartierIitakaDimension K H k := by
  unfold CartierIitakaDimension
  simp_rw [stein_finrank_graded_of_eq_pullback_add_principal K g happ D H φ hD]

/-- Global generation of each multiple is reflected as well as preserved. -/
theorem stein_globallyGenerated_graded_iff_of_eq_pullback_add_principal
    (hsurj : Function.Surjective g) (q : ℕ) :
    CartierIsGloballyGenerated (q • D) ↔ CartierIsGloballyGenerated (q • H) := by
  rw [hD, nsmul_add, ← principalCartierDivisor_power,
    cartierIsGloballyGenerated_principal_shift_iff, ← cartierPullback_nsmul]
  exact cartierIsGloballyGenerated_stein_pullback_iff g happ hsurj (q • H)

end Graded

end MixedFujita
