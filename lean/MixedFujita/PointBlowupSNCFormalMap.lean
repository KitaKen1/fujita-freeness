/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartReindex
public import MixedFujita.SNCStalkIdealCompletedFactor
public import MixedFujita.CenteredPolynomialFormalMap
public import MixedFujita.SuppliedEtaleCartierBlowup

/-! On an actual SNC model through the point blow-up, construct a single
formal map aligned with both the marked divisor and the originally
supplied source completion. Its normal factor and tangent orders come
from the actual point-centre divisor. Every actual Cartier section has
the prescribed leading-form restriction for this same formal map, and
its formal Jacobian is the Taylor image of the actual stalk Jacobian.
The source chart, its actual blow-up coordinate equations and exceptional
stalk ideal are retained for the local chain rule.
Nonvanishing and the component orders of the latter still require the
relative-canonical comparison; they are not assumptions hidden here. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
  {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra

set_option maxHeartbeats 1800000 in
theorem exists_pointBlowup_snc_aligned_formal_map
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (ρ : T ⟶ X) [ρ.IsOver (Spec (.of K))]
    (g : T ⟶ (pointClosureIdeal x).blowUp) (hg : g ≫ (pointClosureIdeal x).blowUpπ = ρ)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (e : Fin r) (hρe : ρ (ξ e) = x)
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = (pointClosureIdeal x).comap ρ)
    (hE0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0)
    (hEe : cartierCoefficient E (ξ e) = 1)
    (P : T) (hP : IsClosed ({P} : Set T)) (heP : P ∈ closure ({ξ e} : Set T))
    (sourceCompletion : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (cX : EtaleChart K X n) (hxcX : x ∈ cX.U) (k : Fin n)
      (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk (g P))
      (β : (pointClosureIdeal x).blowUp.presheaf.stalk (g P) →ₐ[K] T.presheaf.stalk P)
      (c : EtaleChart K T n) (σ : Fin r → Option (Fin n)) (hPc : P ∈ c.U)
      (completion : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk P))
        (T.presheaf.stalk P) ≃ₐ[K] MvPowerSeries (Fin n) K),
      let Taylor := stalkTaylorExpansion P completion
      let ψ := centeredPolynomialFormalMap (Taylor.comp (β.comp τ))
      τ.toRingHom.FormallyEtale ∧ β.toRingHom = (g.stalkMap P).hom ∧
      ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal (g P) =
        Ideal.span {τ (MvPolynomial.X k)} ∧
      (∀ (hq : (pointClosureIdeal x).blowUpπ (g P) = x) (a : MvPolynomial (Fin n) K),
        stalkMapAtEq (pointClosureIdeal x).blowUpπ (g P) x hq
          (etaleChartStalkCoords cX x hxcX a) = τ (polynomialPointBlowupMap k a)) ∧
      IsSNCChart c ξ σ ∧ σ e = some k ∧
      (∀ i, P ∈ closure ({ξ i} : Set T) ↔ ∃ j, σ i = some j) ∧
      (∀ j, Taylor (etaleChartStalkCoords c P hPc (MvPolynomial.X j)) = MvPowerSeries.X j) ∧
      (∀ a, (Taylor a).order = localAdicOrder (T.presheaf.stalk P) a) ∧
      (powerSeriesJacobian ψ).det = Taylor
        (etaleRelativeJacobian β τ (etaleChartStalkCoords c P hPc)
          (etaleChartStalkCoords_formallyEtale c P hPc)).det ∧
      ∃ v : MvPowerSeries (Fin n) K,
        Taylor (β (τ (MvPolynomial.X k))) = MvPowerSeries.X k * v ∧
        ψ (MvPowerSeries.X k) = MvPowerSeries.X k * v ∧
        powerSeriesDivisorRestriction k v ≠ 0 ∧
        (∀ (t : Fin r) (l : Fin n) (hlk : l ≠ k), σ t = some l →
          (powerSeriesDivisorRestriction k v).weightedOrder
            (Pi.single (⟨l, hlk⟩ : {i : Fin n // i ≠ k}) 1) =
              ((cartierCoefficient E (ξ t)).toNat : ℕ∞)) ∧
        ∀ (hq : (pointClosureIdeal x).blowUpπ (g P) = x)
          (D : CartierDivisor X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f)
          (s : Γ(D.sheaf, ⊤)) (m : ℕ), (m : ℕ∞) ≤ cartierSectionVanishingOrder D x s →
          ∃ z : (pointClosureIdeal x).blowUp.presheaf.stalk (g P),
            stalkMapAtEq (pointClosureIdeal x).blowUpπ (g P) x hq
                (cartierLocalCoefficient D x f hf s) = τ (MvPolynomial.X k) ^ m * z ∧
            powerSeriesDivisorRestriction k (Taylor (β z)) =
              powerSeriesDivisorMap ψ k
                (chartShiftedForm k (fun i => MvPowerSeries.constantCoeff
                  (Taylor (β (τ (MvPolynomial.X i.val)))))
                    (homogeneousTaylorForm m (cartierTaylorCoordinates D x f hf sourceCompletion s))) := by
  classical
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let I := pointClosureIdeal x
  let π := I.blowUpπ
  let : I.blowUp.Over (Spec (.of K)) := ⟨π ≫ (X ↘ Spec (.of K))⟩
  have : g.IsOver (Spec (.of K)) := ⟨by
    change g ≫ (π ≫ (X ↘ Spec (.of K))) = T ↘ Spec (.of K)
    rw [← Category.assoc, hg]
    exact HomIsOver.comp_over (f := ρ) (S := Spec (.of K))⟩
  have hq : π (g P) = x := by
    have hm := specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr heP).map ρ.continuous)
    rw [hρe, hx.closure_eq] at hm
    change (g ≫ π) P = x
    rw [hg]
    exact hm
  obtain ⟨cX, hxcX, hall⟩ :=
    smoothCartier_suppliedCompletion_pointBlowup_etale hn x hx sourceCompletion
  obtain ⟨k, τ, hτ, hI, _, hcoord, hres⟩ := hall (g P) hq
  obtain ⟨c, σ, hPc, hc, he, hmem, completion, hTaylor, horder⟩ :=
    exists_centered_snc_completion_with_marked_index ξ hsnc P hP e heP k
  let β := schemeStalkMapAlgHom (K := K) g P
  let Taylor := stalkTaylorExpansion P completion
  let ψ := centeredPolynomialFormalMap (Taylor.comp (β.comp τ))
  have hIT : (effectiveCartierIdealSheaf E hE).stalkIdeal P = Ideal.span {β (τ (MvPolynomial.X k))} := by
    rw [hEI, ← hg, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.stalkIdeal_comap, hI, Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨v, hv, hv0, hvord⟩ := snc_effective_stalkIdeal_completed_normal_factor E hE c ξ hinj hξ
    σ hc hE0 P hPc _ hIT Taylor hTaylor e k he hEe
  refine ⟨cX, hxcX, k, τ, β, c, σ, hPc, completion, hτ, rfl, hI,
    (fun _ => hcoord), hc, he, hmem, hTaylor, horder,
    centeredPolynomialFormalMap_jacobian_det β τ _ _ Taylor hTaylor,
    v, hv, centeredPolynomialFormalMap_normal (Taylor.comp (β.comp τ)) k v hv, hv0, hvord, ?_⟩
  intro hq' D f hf s m hs
  obtain ⟨z, ⟨hz, hzres⟩, _⟩ := hres D f hf s m hs
  refine ⟨z, hz, ?_⟩
  exact centeredPolynomialFormalMap_exceptional_restriction τ (Taylor.comp β) k v hv z _ hzres

end MixedFujita
