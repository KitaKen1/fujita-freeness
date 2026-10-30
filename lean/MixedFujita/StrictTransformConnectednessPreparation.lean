/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformRoundupGeometry
public import MixedFujita.StrictTransformChartsFromConnectedness

/-!
Supply the geometric divisor inputs for strict-transform connectedness from the
original finite functions and their actual principalizing model. The negative
fixed part and relative anti-adjoint are globally generated/nef; the signed
roundup has an exceptional positive part with canonical unit pushforward and a
cut with precisely the non-klt prime threshold. The remaining cohomological
vanishing and the topological connectedness statement are still open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

set_option maxHeartbeats 1600000 in
/-- The actual connectedness model supplies all these divisor conditions internally,
including zero original generators. No nefness, lc bound, exceptional part or unit iso is input. -/
theorem original_function_connectedness_preparation
    {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
    [IsNoetherianRing A] {N : ℕ}
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    {J : Type} [Finite J] (g : J → A)
    {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] [IsNoetherian T]
    [SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K))]
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    [IsProper ρ] (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cT : EtaleChart K T (N + 1)) {r : ℕ} (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K (N + 1) ξ)
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hI : effectiveCartierIdealSheaf G hG = (⨆ j : {j : J // g j ≠ 0},
      effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (g j.1) j.2)) (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ)
    (M : ℕ) (hM : 1 ≤ M) :
    let H := cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
      (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))
    let B := strictTransformConnectednessBoundary ρ hρ cX cT H G M
    (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient B (t : T) = 0) →
    CartierIsGloballyGenerated (-G) ∧ CartierIsNef K (-G) ∧
    CartierIsNef K (-(M • birationalRelativeCanonicalDivisor (N + 1) ρ hρ cX etaleCharts_cover
      cT etaleCharts_cover + B)) ∧
    ∃ (E S : CartierDivisor T) (hE : E.IsEffective) (_ : S.IsEffective),
      (∀ t : CodimensionOnePoint T, cartierCoefficient (E - S) (t : T) =
        ⌈-((cartierCoefficient B (t : T) : ℝ) / (M : ℝ))⌉) ∧
      (∀ t : CodimensionOnePoint T, 0 < cartierCoefficient S (t : T) ↔
        (M : ℤ) ≤ cartierCoefficient B (t : T)) ∧
      (∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) = 0 ∨
        cartierCoefficient S (t : T) = 0) ∧
      (∀ t : CodimensionOnePoint T, Order.coheight (ρ (t : T)) = 1 →
        cartierCoefficient E (t : T) = 0) ∧
      IsIso (effectiveCartierPushforwardUnitMap ρ E hE) := by
  dsimp only
  intro hsupp
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (N + 1) _
  have : IsSeparated (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ)]
    infer_instance
  have hgen := original_function_principalized_neg_globallyGenerated ρ g G hG hI
  refine ⟨hgen, cartierIsGloballyGenerated_isNef hgen, ?_, ?_⟩
  · apply cartierIsGloballyGenerated_isNef
    rw [cartierPullback_principal]
    exact strictTransform_relativeAntiAdjoint_globallyGenerated ρ hρ cX cT _ G hgen M
  · apply exists_strictTransform_roundup_exceptional_pushforward ρ hρ cX cT _ G _ hG M hM
      ξ hinj hξ hsnc hsupp
    apply cartierPullback_isEffective
    exact (CartierDivisor.isEffective_principalCartierDivisor_iff _).mpr
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv (φ (MvPolynomial.X 0)), rfl⟩

end MixedFujita
