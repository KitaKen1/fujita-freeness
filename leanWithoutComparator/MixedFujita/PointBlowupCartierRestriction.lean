/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupGermRestriction
public import MixedFujita.CartierLocalPointBlowup
public import MixedFujita.EtaleChartRegularParameters

/-!
Actual Cartier-section germs on the original scheme point blow-up, at every point of
the exceptional fibre, including nonclosed points. Compatible completion coordinates are
constructed from an etale chart, and at smooth closed points from the geometric dimension.
The actual exceptional ideal, its regular generator, the actual projection stalk map,
and the unique m-th transform's leading-form restriction are outputs. Comparison with an
arbitrary previously supplied completion coordinate system is a separate assertion.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
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

set_option maxHeartbeats 800000 in
theorem etaleChart_cartierSections_pointBlowup
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (α : X.presheaf.stalk x →ₐ[K] K) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      (∀ i, stalkTaylorExpansion x e
        (etaleChartCenteredStalkCoords c x hx α (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x),
        ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →+* (pointClosureIdeal x).blowUp.presheaf.stalk q),
          ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
            Ideal.span {τ (MvPolynomial.X k)} ∧
          τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
          ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
            (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
            ∃! r : (pointClosureIdeal x).blowUp.presheaf.stalk q,
              stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (cartierLocalCoefficient D x f hf s) =
                  τ (MvPolynomial.X k) ^ m * r ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) r =
                pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
                  (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s))) := by
  obtain ⟨e, hX, hord⟩ := etaleChart_exists_taylorCoordinates c x hx α
  have horder : ∀ r, (stalkTaylorExpansion x e r).order =
      localAdicOrder (X.presheaf.stalk x) r := hord
  refine ⟨e, hX, ?_⟩
  intro q hq
  obtain ⟨k, τ, hI, hreg, -, hall⟩ := pointBlowup_germs_exceptional_restriction x
    (etaleChartCenteredStalkCoords c x hx α) (stalkTaylorExpansion x e) hX horder
    (etaleChart_maximalIdeal_eq_span c x hx α) q hq
  refine ⟨k, τ, hI, hreg, ?_⟩
  intro D f hf s m hs
  apply hall (cartierLocalCoefficient D x f hf s) m
  rw [horder, ← cartierSectionVanishingOrder_eq_localCoefficient D x f hf]
  exact hs

theorem smoothCartier_closedPoint_pointBlowup [IsAlgClosed K]
    [Smooth (X ↘ Spec (.of K))] (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
      ∀ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x),
        ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →+* (pointClosureIdeal x).blowUp.presheaf.stalk q),
          ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
            Ideal.span {τ (MvPolynomial.X k)} ∧
          τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
          ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
            (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
            ∃! r : (pointClosureIdeal x).blowUp.presheaf.stalk q,
              stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (cartierLocalCoefficient D x f hf s) =
                  τ (MvPolynomial.X k) ^ m * r ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) r =
                pointBlowupExceptionalEvaluation τ k (projectiveDehomogenize K k
                  (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf e s))) := by
  obtain ⟨U, hU, hxU, α, g, hg, -⟩ :=
    geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart (K := K) n hn x hx
  have hg' : g.toRingHom.FormallyEtale := by
    let _ := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, U) := hg
    exact Algebra.Etale.formallyEtale
  let c : EtaleChart K X n := ⟨U, hU, ⟨⟨x, hxU⟩⟩, g, hg'⟩
  obtain ⟨e, -, h⟩ := etaleChart_cartierSections_pointBlowup c x hxU α
  exact ⟨e, h⟩

end MixedFujita
