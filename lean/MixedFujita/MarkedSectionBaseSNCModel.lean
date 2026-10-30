/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupMarkedEquality
public import MixedFujita.SectionBaseSNCModel

/-! Construct the actual section-base SNC model together with a marked
prime above the specified smooth closed point. The fixed coefficient nh,
discrepancy coefficient n-1 and exact threshold equality hold at that same
prime. The model, point blow-up domination, fixed part and moving global
generation are all constructed; no model or discrepancy input is assumed.
The marked prime is the only point over its image on the point blow-up.
Strict inequalities at the other primes are a separate remaining task. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [IsLocallyNoetherian X] [IsProper (X ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 1200000 in
theorem exists_sectionBase_snc_model_with_pointBlowup_equality {J : Type*} [Finite J] [Nonempty J]
    (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n) (x : X) (hx : IsClosed ({x} : Set X))
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (s : J → Γ(M.sheaf, ⊤))
    (hs : ∀ j, s j ≠ 0) (h : ℕ) (hh : 0 < h)
    (horders : ∀ j, cartierSectionVanishingOrder M x (s j) = ((n * h : ℕ) : ℕ∞)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (.of K))) (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (.of K))) (_ : IsProper (T ↘ Spec (.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (.of K))) (_ : IsProper ρ) (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T) (k₀ : Fin r)
      (G : CartierDivisor T) (hG : G.IsEffective),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (t : T) = 0) ∧
      effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) ∧
      CartierIsGloballyGenerated (cartierPullback ρ M - G) ∧
      (∃ g : T ⟶ (pointClosureIdeal x).blowUp, g ≫ (pointClosureIdeal x).blowUpπ = ρ ∧
        Order.coheight (g (ξ k₀)) = 1 ∧ Function.Bijective (g.stalkMap (ξ k₀)) ∧
        (∀ t : T, g t = g (ξ k₀) → t = ξ k₀)) ∧
      ρ (ξ k₀) = x ∧ cartierCoefficient G (ξ k₀) = ((n * h : ℕ) : ℤ) ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
        cT etaleCharts_cover) (ξ k₀) = (n : ℤ) - 1 ∧
      cartierCoefficient G (ξ k₀) = (h : ℤ) *
        (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (ξ k₀)) := by
  have hdim : 0 < topologicalKrullDim X := by
    rw [hn]
    exact_mod_cast (show 0 < n by omega)
  let 𝔟 : Fin 1 → X.IdealSheafData := fun _ => pointClosureIdeal x
  have h𝔟 : ∀ j, genericPoint X ∉ ((𝔟 j).support : Set X) := fun _ =>
    pointClosureIdeal_genericPoint_notMem hdim x hx
  obtain ⟨T, _, _, _, _, hTP, ρ, _, _, _, _, hρ, cT, r, ξ,
      hinj, hcoh, hsnc, hTB, _, haux, G, hG, hGI, hG0, _, _, hGG, _⟩ :=
    exists_sectionBase_snc_model c₀ 1 1
      (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0) M s hs 𝔟 h𝔟
  obtain ⟨g, hg⟩ := (haux 0).2.1
  obtain ⟨k₀, hkx, hkgcod, hkbij, hkuniq, hkG, hkD, heq⟩ :=
    smooth_closedPoint_principalized_sectionBase_marked_equality hn hn1 x hx ρ hρ g hg
      c₀ cT M s hs h hh horders G hG hGI ξ hG0
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, hTP, ρ,
    inferInstance, inferInstance, inferInstance, inferInstance, hρ, cT, r, ξ, k₀, G, hG,
    hinj, hcoh, hsnc, hTB, hGI, hG0, hGG, ⟨g, hg, hkgcod, hkbij, hkuniq⟩, hkx, hkG, hkD, heq⟩

end MixedFujita
