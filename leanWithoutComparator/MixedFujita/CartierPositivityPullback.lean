/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierBigDefinition
public import MixedFujita.ExceptionalCartierSections
public import MixedFujita.CartierBirationalZeroDivisors
public import MixedFujita.PrincipalizedGlobalGeneration

/-!
Nefness, bigness and finiteness of sections under proper birational pullback (step 12).

* A Cartier divisor with a nef positive multiple is nef; hence the pullback along any dominant
  morphism of a divisor with a globally generated positive multiple is nef.
* For a proper birational morphism ρ : T → X of normal schemes over a field, the sections of ρ*D
  are the pullbacks of the sections of D. Hence finite-dimensionality of the sections passes from
  D to ρ*D, and, when T and X have the same dimension, bigness passes from D to ρ*D.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra functionFieldBaseScalarTower

omit [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] in
/-- A Cartier divisor with a nef positive multiple is nef. -/
theorem cartierIsNef_of_nsmul {D : CartierDivisor X} (k : ℕ) (hk : 1 ≤ k)
    (h : CartierIsNef K (k • D)) : CartierIsNef K D := by
  intro C _ _ _ _ hC φ hφ
  have h1 := h C hC φ hφ
  rw [cartierCurvePullbackDegree_nsmul (K := K) hC] at h1
  have hk' : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  exact (mul_nonneg_iff_of_pos_left hk').mp h1

omit [X.Over (Spec (CommRingCat.of K))] in
/-- The pullback of a Cartier divisor with a globally generated positive multiple is nef. -/
theorem cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul (ρ : T ⟶ X) [IsDominant ρ]
    (D : CartierDivisor X) (k : ℕ) (hk : 1 ≤ k) (hD : CartierIsGloballyGenerated (k • D)) :
    CartierIsNef K (cartierPullback ρ D) := by
  apply cartierIsNef_of_nsmul k hk
  rw [← cartierPullback_nsmul]
  exact cartierIsGloballyGenerated_isNef (cartierIsGloballyGenerated_cartierPullback ρ _ hD)

variable [IsLocallyNoetherian X] [IsLocallyNoetherian T]

omit [IsLocallyNoetherian T] in
/-- For a proper birational morphism to a normal scheme, finite-dimensionality of the sections
passes to the pullback. -/
theorem finiteDimensional_sections_cartierPullback
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ)) (D : CartierDivisor X)
    (hfin : FiniteDimensional K Γ(D.sheaf, ⊤)) :
    FiniteDimensional K Γ((cartierPullback ρ D).sheaf, ⊤) := by
  let e₁ : Γ(D.sheaf, ⊤) ≃ₗ[K] cartierSectionSpace K D :=
    LinearEquiv.ofInjective ((cartierSectionRational D).restrictScalars K)
      (cartierSectionRational_injective D)
  let e₂ : Γ((cartierPullback ρ D).sheaf, ⊤) ≃ₗ[K] cartierSectionSpace K (cartierPullback ρ D) :=
    LinearEquiv.ofInjective ((cartierSectionRational (cartierPullback ρ D)).restrictScalars K)
      (cartierSectionRational_injective (cartierPullback ρ D))
  have h1 : FiniteDimensional K (cartierSectionSpace K D) := e₁.finiteDimensional
  have h2 : FiniteDimensional K (cartierSectionSpace K (cartierPullback ρ D)) := by
    rw [cartierSectionSpace_cartierPullback K hnorm ρ hρ.2 D]
    infer_instance
  exact e₂.symm.finiteDimensional

/-- For a proper birational morphism of normal schemes of the same dimension, the pullback of a
big divisor is big. -/
theorem cartierIsBig_cartierPullback
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (hdim : topologicalKrullDim T = topologicalKrullDim X) {D : CartierDivisor X}
    (hD : CartierIsBig K D) : CartierIsBig K (cartierPullback ρ D) := by
  obtain ⟨d, hd, c, hc, hfreq⟩ := hD
  refine ⟨d, hdim.trans hd, c, hc, hfreq.mono fun m hm => ?_⟩
  have h := finrank_sections_effective_exceptional_cartierPullback K hnorm hnormT ρ hρ 0
    CartierDivisor.isEffective_zero (fun t _ => cartierCoefficient_zero _) (m • D)
  rw [add_zero, cartierPullback_nsmul] at h
  rw [h]
  exact hm

end MixedFujita
