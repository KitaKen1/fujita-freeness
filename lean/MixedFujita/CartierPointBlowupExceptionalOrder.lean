/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupExceptionalStalkDVR
public import MixedFujita.PointBlowupCartierRestriction

/-! Exact exceptional DVR orders of actual Cartier-section germs. The compatible
Taylor coordinates are constructed from an étale chart, and at a smooth closed
point from the geometric dimension. No discrepancy comparison is assumed. -/

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

theorem etaleChart_exists_exceptional_dvr_with_section_orders
    [LocallyOfFiniteType (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (α : X.presheaf.stalk x →ₐ[K] K)
    (k : Fin n) :
    ∃ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x)
        (hB : IsDomain ((pointClosureIdeal x).blowUp.presheaf.stalk q)),
      @IsDiscreteValuationRing ((pointClosureIdeal x).blowUp.presheaf.stalk q) _ hB ∧
      ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
        (s : Γ(D.sheaf, ⊤)) (d : ℕ), cartierSectionVanishingOrder D x s = (d : ℕ∞) →
        localAdicOrder ((pointClosureIdeal x).blowUp.presheaf.stalk q)
          (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq
            (cartierLocalCoefficient D x f hf s)) = (d : ℕ∞) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  obtain ⟨e, hX, hord⟩ := etaleChart_exists_taylorCoordinates c x hx α
  have horder : ∀ r, (stalkTaylorExpansion x e r).order =
      localAdicOrder (X.presheaf.stalk x) r := hord
  obtain ⟨q, hq, hB, hDVR, hall⟩ := pointBlowup_exists_exceptional_dvr_stalk x
    (etaleChartCenteredStalkCoords c x hx α) (stalkTaylorExpansion x e) hX horder
    (etaleChart_maximalIdeal_eq_span c x hx α) k
  refine ⟨q, hq, hB, hDVR, ?_⟩
  intro D f hf s d hs
  apply hall (cartierLocalCoefficient D x f hf s) d
  rw [← cartierSectionVanishingOrder_eq_localCoefficient D x f hf]
  exact hs

theorem smooth_closedPoint_exists_exceptional_dvr_with_section_orders [IsAlgClosed K]
    [Smooth (X ↘ Spec (.of K))] (hn : topologicalKrullDim X = n)
    (x : X) (hx : IsClosed ({x} : Set X)) (k : Fin n) :
    ∃ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x)
        (hB : IsDomain ((pointClosureIdeal x).blowUp.presheaf.stalk q)),
      @IsDiscreteValuationRing ((pointClosureIdeal x).blowUp.presheaf.stalk q) _ hB ∧
      ∀ (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
        (s : Γ(D.sheaf, ⊤)) (d : ℕ), cartierSectionVanishingOrder D x s = (d : ℕ∞) →
        localAdicOrder ((pointClosureIdeal x).blowUp.presheaf.stalk q)
          (stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq
            (cartierLocalCoefficient D x f hf s)) = (d : ℕ∞) := by
  obtain ⟨U, hU, hxU, α, g, hg, -⟩ :=
    geometricSmoothScheme_closedPoint_exists_centeredAffineEtaleChart (K := K) n hn x hx
  have hg' : g.toRingHom.FormallyEtale := by
    let _ := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, U) := hg
    exact Algebra.Etale.formallyEtale
  let c : EtaleChart K X n := ⟨U, hU, ⟨⟨x, hxU⟩⟩, g, hg'⟩
  exact etaleChart_exists_exceptional_dvr_with_section_orders c x hxU α k

end MixedFujita
