/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeneralSectionBaseThresholdModel
public import MixedFujita.ThresholdBaseModelLifting

/-! The original ThresholdBaseModelStatement in every positive dimension.
Ampleness supplies properness; the actual SNC model, fixed part, marked
equality and all-prime strict inequalities are constructed. The original
leading-form threshold and section orders are the only local inputs. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))] [IsLocallyNoetherian X]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 1800000 in
theorem thresholdBaseModel_positive_dimension
    (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n) (c₀ : EtaleChart K X n)
    (A : CartierDivisor X) (hA : CartierIsAmpleSum K A)
    (x : X) (hx : IsClosed ({x} : Set X))
    (f : X.functionFieldˣ) (hf : A.IsLocalEquationAt x f)
    (coordinates : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (e h : ℕ) (hh : 0 < h) (he : e < h)
    {ι : Type} [Fintype ι] [Nonempty ι] (s : ι → Γ((e • A).sheaf, ⊤))
    (hs : ∀ l, s l ≠ 0)
    (horders : ∀ l, cartierSectionVanishingOrder _ x (s l) = ((n * h : ℕ) : ℕ∞))
    (hthreshold : ProjectiveThresholdCondition (fun l => homogeneousTaylorForm (n * h)
      (cartierTaylorCoordinates _ x (f ^ e) (cartierLocalEquation_pow A x f hf e)
        coordinates (s l))) h) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T)
            (_ : IsLocallyNoetherian T) (_ : T.Over (Spec (CommRingCat.of K)))
            (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
            (_ : IsProper (T ↘ Spec (CommRingCat.of K))) (ρ : T ⟶ X) (_ : IsDominant ρ)
            (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
            (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
            (cT : EtaleChart K T n) (r : ℕ) (ξT : Fin r → T) (k₀ : Fin r) (G : CartierDivisor T),
            Function.Injective ξT ∧ (∀ k, Order.coheight (ξT k) = 1) ∧ IsSNCFamily K n ξT ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient (crepantBoundaryCartier ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (t : T) = 0) ∧
            G.IsEffective ∧
            (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξT →
              cartierCoefficient G (t : T) = 0) ∧
            CartierIsGloballyGenerated (cartierPullback ρ (e • A) - G) ∧
            ρ (ξT k₀) = x ∧
            cartierCoefficient G (ξT k₀) =
              (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                cT etaleCharts_cover) (ξT k₀)) ∧
            ∀ t : CodimensionOnePoint T,
              (closure ({(t : T)} : Set T) ∩ closure ({ξT k₀} : Set T)).Nonempty →
              cartierCoefficient G (t : T) ≤
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) ∧
              (cartierCoefficient G (t : T) =
                (h : ℤ) * (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
                  (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
                  cT etaleCharts_cover) (t : T)) → (t : T) = ξT k₀) := by
  classical
  obtain ⟨m, hm, N, ιX, hιX, hbase, -⟩ := cartierIsAmpleProj_of_isAmpleSum hA
  let : IsClosedImmersion ιX := hιX
  have := polynomialProjectiveToBase_isProper N K
  have : IsProper (X ↘ Spec (.of K)) := by
    rw [← hbase]
    infer_instance
  obtain ⟨T, _, _, _, _, _, ρ, _, _, _, _, hρ, cT, r, ξ, k₀, G, hG,
      hinj, hcoh, hsnc, hTB, -, hG0, hGG, hρx, heq, hall⟩ :=
    exists_sectionBase_snc_model_with_pointBlowup_threshold hn hn1 x hx c₀ (e • A) s hs h hh
      horders (f ^ e) (cartierLocalEquation_pow A x f hf e) coordinates hthreshold
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ρ, inferInstance, inferInstance, inferInstance, hρ, cT, r, ξ, k₀, G,
    hinj, hcoh, hsnc, hTB, hG, hG0, hGG, hρx, heq, hall⟩

/-- The full original threshold-base-model statement, with no extra local
geometric or formal-restriction hypotheses. -/
theorem thresholdBaseModelStatement_holds : ThresholdBaseModelStatement := by
  intro K _ _ _ _ X _ _ n hn hn1 _ _ c₀ A hA x hx f hf coordinates e h hh he ι _ _ s hs horders hthreshold
  exact thresholdBaseModel_positive_dimension hn hn1 c₀ A hA x hx f hf coordinates e h hh he s hs horders hthreshold

end MixedFujita
