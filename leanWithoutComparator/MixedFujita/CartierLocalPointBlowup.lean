/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupLeadingRestriction
public import MixedFujita.EtaleChartTaylorCoordinates
public import MixedFujita.CartierVanishingOrder
public import MixedFujita.GeometricSmoothTaylor

/-!
Actual Cartier-section germs on the point-blow-up of the actual local ring.
An etale chart and a rational local point construct compatible completion coordinates.
One actual chart-ring homomorphism works for every Cartier divisor, frame, section and
order bound. Its unique strict-transform representative has the leading-form exceptional
restriction. Transport to the global scheme blow-up and its exceptional prime is separate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of K))] {n : ℕ}
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra

theorem cartierSection_localPointBlowup_exceptional_restriction
    (x : X) (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, stalkTaylorExpansion x e (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (stalkTaylorExpansion x e r).order = localAdicOrder (X.presheaf.stalk x) r)
    (k : Fin n) :
    ∃ τ : MvPolynomial (Fin n) K →+*
        affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (ψ (MvPolynomial.X k)),
      τ (MvPolynomial.X k) = algebraMap (X.presheaf.stalk x) _ (ψ (MvPolynomial.X k)) ∧
      (∀ g, τ (polynomialPointBlowupMap k g) = algebraMap (X.presheaf.stalk x) _ (ψ g)) ∧
      ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
        (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
        ∃! q : affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (ψ (MvPolynomial.X k)),
          algebraMap (X.presheaf.stalk x) _ (cartierLocalCoefficient D x f hf s) =
              τ (MvPolynomial.X k) ^ m * q ∧
            Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
              pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
                (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s))) := by
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ (stalkTaylorExpansion x e) hX hord
  refine ⟨localPointBlowupPolynomialMap _ ψ hψ k,
    localPointBlowupPolynomialMap_X_self _ ψ hψ k,
    localPointBlowupPolynomialMap_substitution _ ψ hψ k, ?_⟩
  intro D f hf s m hs
  have hs' : (m : ℕ∞) ≤ (stalkTaylorExpansion x e (cartierLocalCoefficient D x f hf s)).order := by
    rw [hord, ← cartierSectionVanishingOrder_eq_localCoefficient D x f hf]
    exact hs
  exact localPointBlowup_germ_exceptional_restriction ψ (stalkTaylorExpansion x e) hX hord
    k (cartierLocalCoefficient D x f hf s) m hs'

theorem etaleChart_cartierSections_localPointBlowup
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (α : X.presheaf.stalk x →ₐ[K] K) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      (∀ i, stalkTaylorExpansion x e
        (etaleChartCenteredStalkCoords c x hx α (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ k : Fin n, ∃ τ : MvPolynomial (Fin n) K →+*
          affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
            (etaleChartCenteredStalkCoords c x hx α (MvPolynomial.X k)),
        τ (MvPolynomial.X k) = algebraMap (X.presheaf.stalk x) _
          (etaleChartCenteredStalkCoords c x hx α (MvPolynomial.X k)) ∧
        (∀ g, τ (polynomialPointBlowupMap k g) = algebraMap (X.presheaf.stalk x) _
          (etaleChartCenteredStalkCoords c x hx α g)) ∧
        ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
          (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
          ∃! q : affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (etaleChartCenteredStalkCoords c x hx α (MvPolynomial.X k)),
            algebraMap (X.presheaf.stalk x) _ (cartierLocalCoefficient D x f hf s) =
                τ (MvPolynomial.X k) ^ m * q ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
                pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
                  (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s))) := by
  obtain ⟨e, hX, hord⟩ := etaleChart_exists_taylorCoordinates c x hx α
  exact ⟨e, hX, fun k => cartierSection_localPointBlowup_exceptional_restriction x
    (etaleChartCenteredStalkCoords c x hx α) e hX hord k⟩

theorem smoothCartier_closedPoint_localPointBlowup [IsAlgClosed K]
    [Smooth (X ↘ Spec (.of K))] (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
      (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K),
      (∀ i, stalkTaylorExpansion x e (ψ (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ k : Fin n, ∃ τ : MvPolynomial (Fin n) K →+*
          affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (ψ (MvPolynomial.X k)),
        τ (MvPolynomial.X k) = algebraMap (X.presheaf.stalk x) _ (ψ (MvPolynomial.X k)) ∧
        (∀ g, τ (polynomialPointBlowupMap k g) = algebraMap (X.presheaf.stalk x) _ (ψ g)) ∧
        ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
          (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
          ∃! q : affineBlowUpAlgebra (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
              (ψ (MvPolynomial.X k)),
            algebraMap (X.presheaf.stalk x) _ (cartierLocalCoefficient D x f hf s) =
                τ (MvPolynomial.X k) ^ m * q ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
                pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
                  (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s))) := by
  obtain ⟨U, hU, hxU, α, g, hg, -⟩ :=
    geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart (K := K) n hn x hx
  have hg' : g.toRingHom.FormallyEtale := by
    let _ := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, U) := hg
    exact Algebra.Etale.formallyEtale
  let c : EtaleChart K X n := ⟨U, hU, ⟨⟨x, hxU⟩⟩, g, hg'⟩
  obtain ⟨e, hX, h⟩ := etaleChart_cartierSections_localPointBlowup c x hxU α
  exact ⟨etaleChartCenteredStalkCoords c x hxU α, e, hX, h⟩

end MixedFujita
