/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AlignedEtalePointBlowup
public import MixedFujita.CartierLocalPointBlowup

/-! A supplied completion determines an actual source etale chart whose
point-blow-up coordinates are formally etale and have the actual Cartier
section restriction prescribed by that same completion. The coordinate
map, source chart, factorization and exceptional restriction are produced
together at every point of the actual exceptional fibre. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (.of K))] {n : ℕ}
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

set_option maxHeartbeats 1000000 in
theorem etaleChart_suppliedCompletion_cartier_pointBlowup_etale [PerfectField K]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (hxc : IsClosed ({x} : Set X))
    (α : X.presheaf.stalk x →ₐ[K] K)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    ∃ (c' : EtaleChart K X n) (hx' : x ∈ c'.U),
      ∀ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x),
        let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
          ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
        ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q),
          τ.toRingHom.FormallyEtale ∧
          ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
            Ideal.span {τ (MvPolynomial.X k)} ∧
          τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
          (∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq
            (etaleChartStalkCoords c' x hx' g) = τ (polynomialPointBlowupMap k g)) ∧
          ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
            (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
            ∃! z : (pointClosureIdeal x).blowUp.presheaf.stalk q,
              stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (cartierLocalCoefficient D x f hf s) =
                τ (MvPolynomial.X k) ^ m * z ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) z =
                pointBlowupExceptionalEvaluation τ.toRingHom k
                  (projectiveDehomogenize K k (homogeneousTaylorForm m
                    (cartierTaylorCoordinates D x f hf e s))) := by
  obtain ⟨ψ, E, hE, hall⟩ := suppliedCompletion_pointBlowup_exists_etale_restriction c x hx hxc α e
  let c' := etaleChartOfToAffineSpace E.U ⟨⟨x, E.mem⟩⟩ E.v E.etale
  have hψ : etaleChartStalkCoords c' x E.mem = ψ := by
    ext i
    change X.presheaf.germ E.U.1 x E.mem
      ((etaleChartOfToAffineSpace E.U ⟨⟨x, E.mem⟩⟩ E.v E.etale).coords (MvPolynomial.X i)) = _
    rw [etaleChartOfToAffineSpace_coords]
    exact hE i
  refine ⟨c', E.mem, ?_⟩
  intro q hq
  obtain ⟨k, τ, hτ, hI, hreg, hcomp, hres⟩ := hall q hq
  refine ⟨k, τ, hτ, hI, hreg, ?_, ?_⟩
  · intro g
    rw [hψ]
    exact hcomp g
  · intro D f hf s m hs
    apply hres (cartierLocalCoefficient D x f hf s) m
    rwa [← cartierSectionVanishingOrder_eq_localCoefficient D x f hf]

set_option maxHeartbeats 1000000 in
theorem smoothCartier_suppliedCompletion_pointBlowup_etale [IsAlgClosed K]
    [Smooth (X ↘ Spec (.of K))] (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X))
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    ∃ (c : EtaleChart K X n) (hx' : x ∈ c.U),
      ∀ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x),
        let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
          ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
        ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q),
          τ.toRingHom.FormallyEtale ∧
          ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
            Ideal.span {τ (MvPolynomial.X k)} ∧
          τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
          (∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq
            (etaleChartStalkCoords c x hx' g) = τ (polynomialPointBlowupMap k g)) ∧
          ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
            (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
            ∃! z : (pointClosureIdeal x).blowUp.presheaf.stalk q,
              stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (cartierLocalCoefficient D x f hf s) =
                τ (MvPolynomial.X k) ^ m * z ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) z =
                pointBlowupExceptionalEvaluation τ.toRingHom k
                  (projectiveDehomogenize K k (homogeneousTaylorForm m
                    (cartierTaylorCoordinates D x f hf e s))) := by
  let := geometricSmoothScheme_relativeDimension (K := K) n hn
  obtain ⟨U, hU, hxU, α, g, hg, -⟩ :=
    geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart (K := K) n hn x hx
  have hg' : g.toRingHom.FormallyEtale := by
    let _ := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, U) := hg
    exact Algebra.Etale.formallyEtale
  let c : EtaleChart K X n := ⟨U, hU, ⟨⟨x, hxU⟩⟩, g, hg'⟩
  exact etaleChart_suppliedCompletion_cartier_pointBlowup_etale c x hxU hx α e

end MixedFujita
