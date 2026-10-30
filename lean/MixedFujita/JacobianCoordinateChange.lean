/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricJacobianBound

/-!
The log discrepancy A(v) = Σ w + v(det J) of a monomial test valuation does not depend on the
completion coordinates at the image point. By the chain rule the Jacobian of a composite is
J(ψ₂ ∘ ψ₁) = ψ₂(J(ψ₁)) J(ψ₂), so det J(ψ₂ ∘ ψ₁) = ψ₂(det J(ψ₁)) det J(ψ₂). For an automorphism θ
the identity J(θ⁻¹ ∘ θ) = 1 makes det J(θ) a unit, and a unit has weighted order zero, so
v(det J(ψ ∘ θ)) = v(det J(ψ)). Changing the coordinates at ρ(p) replaces the completed stalk map
ψ by ψ ∘ θ with θ = e ∘ e'⁻¹, so A(v) is determined by ρ, p, the coordinates at p and the
weights.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPowerSeries Finset
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section PowerSeries

variable {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]

/-- The Jacobian of a composite. -/
theorem powerSeriesJacobian_comp [CharZero K]
    (ψ₁ ψ₂ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) :
    powerSeriesJacobian (ψ₂.comp ψ₁) =
      (ψ₂ : MvPowerSeries σ K →+* MvPowerSeries σ K).mapMatrix (powerSeriesJacobian ψ₁) *
        powerSeriesJacobian ψ₂ := by
  refine Matrix.ext fun l j => ?_
  rw [Matrix.mul_apply]
  change pderiv j (ψ₂ (ψ₁ (X l))) = ∑ k, ψ₂ (pderiv k (ψ₁ (X l))) * powerSeriesJacobian ψ₂ k j
  exact powerSeries_chainRule ψ₂ (constantCoeff_algHom_X ψ₂) (ψ₁ (X l)) j

/-- det J(ψ₂ ∘ ψ₁) = ψ₂(det J(ψ₁)) · det J(ψ₂). -/
theorem powerSeriesJacobian_det_comp [CharZero K]
    (ψ₁ ψ₂ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) :
    (powerSeriesJacobian (ψ₂.comp ψ₁)).det =
      ψ₂ (powerSeriesJacobian ψ₁).det * (powerSeriesJacobian ψ₂).det := by
  rw [powerSeriesJacobian_comp, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det (ψ₂ : MvPowerSeries σ K →+* MvPowerSeries σ K) _).symm

omit [Fintype σ] in
theorem powerSeriesJacobian_id :
    powerSeriesJacobian (AlgHom.id K (MvPowerSeries σ K)) = 1 := by
  refine Matrix.ext fun i j => ?_
  change pderiv j (X i) = (1 : Matrix σ σ (MvPowerSeries σ K)) i j
  rw [pderiv_X, Matrix.one_apply, Pi.single_apply]

/-- The Jacobian determinant of an automorphism is a unit. -/
theorem isUnit_det_powerSeriesJacobian_of_algEquiv [CharZero K]
    (θ : MvPowerSeries σ K ≃ₐ[K] MvPowerSeries σ K) :
    IsUnit (powerSeriesJacobian θ.toAlgHom).det := by
  have h := powerSeriesJacobian_det_comp θ.toAlgHom θ.symm.toAlgHom
  have hid : θ.symm.toAlgHom.comp θ.toAlgHom = AlgHom.id K (MvPowerSeries σ K) := by
    ext x
    simp
  rw [hid, powerSeriesJacobian_id, Matrix.det_one] at h
  have hu : IsUnit (θ.symm.toAlgHom (powerSeriesJacobian θ.toAlgHom).det) :=
    IsUnit.of_mul_eq_one _ h.symm
  have hu' := hu.map θ.toAlgHom
  simpa using hu'

/-- Precomposing with an automorphism does not change v(det J). -/
theorem weightedOrder_det_powerSeriesJacobian_comp_algEquiv [CharZero K] (w : σ → ℕ)
    (ψ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K)
    (θ : MvPowerSeries σ K ≃ₐ[K] MvPowerSeries σ K) :
    (powerSeriesJacobian (ψ.comp θ.toAlgHom)).det.weightedOrder w =
      (powerSeriesJacobian ψ).det.weightedOrder w := by
  rw [powerSeriesJacobian_det_comp, weightedOrder_mul,
    weightedOrder_eq_zero_of_isUnit w ((isUnit_det_powerSeriesJacobian_of_algEquiv θ).map ψ),
    zero_add]

end PowerSeries

universe u

variable {K : Type u} [Field K] {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower

/-- Changing the coordinates at ρ(p) precomposes the completed stalk map with an
automorphism. -/
theorem schemeCompletedStalkMap_change_coordinates (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ez ez' : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    schemeCompletedStalkMap ρ p ez' ep =
      (schemeCompletedStalkMap ρ p ez ep).comp (ez'.symm.trans ez).toAlgHom := by
  ext x
  simp [schemeCompletedStalkMap]

/-- The log discrepancy Σ w + v(det J) of a test valuation does not depend on the coordinates at
ρ(p). -/
theorem schemeCompletedStalkMap_jacobian_weightedOrder_eq [CharZero K] (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ez ez' : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K) (w : Fin n → ℕ) :
    (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez' ep)).det.weightedOrder w =
      (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w := by
  rw [schemeCompletedStalkMap_change_coordinates ρ p ez ez' ep,
    weightedOrder_det_powerSeriesJacobian_comp_algEquiv]

end MixedFujita
