/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearLocalParameters
public import MixedFujita.EtaleChartRegularParameters

/-! Construct actual local parameters and compatible completion coordinates
whose leading forms agree with any supplied completion coordinates. Match the
linear tangent matrix; higher-order coordinate changes have no effect on
leading forms. No invariance theorem for projective thresholds is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
open MvPowerSeries IsLocalRing
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

set_option maxHeartbeats 600000 in
theorem etaleChart_exists_completionCoordinates_with_supplied_leading_forms
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (α : X.presheaf.stalk x →ₐ[K] K)
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
      MvPowerSeries (Fin n) K) :
    ∃ (e' : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
        MvPowerSeries (Fin n) K) (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x),
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)) ∧
      (∀ i, stalkTaylorExpansion x e' (ψ (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ (r : X.presheaf.stalk x) (m : ℕ), (m : ℕ∞) ≤ localAdicOrder (X.presheaf.stalk x) r →
        homogeneousTaylorForm m (stalkTaylorExpansion x e' r) =
          homogeneousTaylorForm m (stalkTaylorExpansion x e r) := by
  obtain ⟨e₀, hX, hord⟩ := etaleChart_exists_taylorCoordinates c x hx α
  have horder (r : X.presheaf.stalk x) :
      (stalkTaylorExpansion x e₀ r).order = localAdicOrder (X.presheaf.stalk x) r := hord r
  let θ := e₀.symm.trans e
  let A := powerSeriesTangentMatrix θ
  have hA : IsUnit A := powerSeriesTangentMatrix_isUnit θ
  let L := powerSeriesLinearEquiv A hA
  obtain ⟨ψ, hmax, hψ⟩ := linear_aligned_local_parameters
    (etaleChartCenteredStalkCoords c x hx α) (stalkTaylorExpansion x e₀) hX
    (etaleChart_maximalIdeal_eq_span c x hx α) A hA
  refine ⟨e₀.trans L, ψ, hmax, hψ, ?_⟩
  intro r m hr
  have h := homogeneousTaylorForm_algEquiv_tangent θ m (stalkTaylorExpansion x e₀ r)
    (by rwa [horder])
  have heθ : θ (stalkTaylorExpansion x e₀ r) = stalkTaylorExpansion x e r := by
    change e (e₀.symm (e₀ (algebraMap (X.presheaf.stalk x) _ r))) = _
    rw [e₀.symm_apply_apply]
    rfl
  rw [heθ] at h
  exact h.symm

theorem alignedCompletionCoordinates_cartier_leading_forms [IsIntegral X]
    (x : X)
    (e e' : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
      MvPowerSeries (Fin n) K)
    (hforms : ∀ (r : X.presheaf.stalk x) (m : ℕ),
      (m : ℕ∞) ≤ localAdicOrder (X.presheaf.stalk x) r →
      homogeneousTaylorForm m (stalkTaylorExpansion x e' r) =
        homogeneousTaylorForm m (stalkTaylorExpansion x e r))
    (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
    (s : Γ(D.sheaf, ⊤)) (m : ℕ) (hs : (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s) :
    homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e' s) =
      homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s) := by
  have hs' : (m : ℕ∞) ≤ localAdicOrder (X.presheaf.stalk x) (cartierLocalCoefficient D x f hf s) := by
    rwa [← cartierSectionVanishingOrder_eq_localCoefficient D x f hf]
  exact hforms (cartierLocalCoefficient D x f hf s) m hs'

end MixedFujita
