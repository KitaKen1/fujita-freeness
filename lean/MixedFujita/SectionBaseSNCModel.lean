/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBaseIdeal

/-!
Construct the actual principalizing half of the threshold base model from the given sections.
The base ideal, smooth proper SNC model, effective fixed part and global generation of the
moving part are outputs, rather than assumptions. Finitely many prescribed blow-ups are
dominated. The threshold-to-discrepancy inequalities are not asserted here.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]

/-- Actual resolution and fixed-part generation for the supplied finite section family. -/
theorem exists_sectionBase_snc_model {J μ : Type*} [Finite J] [Nonempty J] [Finite μ]
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D M : CartierDivisor X)
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0) (𝔟 : μ → X.IdealSheafData)
    (h𝔟 : ∀ j, genericPoint X ∉ ((𝔟 j).support : Set X)) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (_ : IsProper (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K)))
      (_ : IsProper ρ) (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : J) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j)))
          (t : T) = 0) ∧
      (∀ j : μ, ((𝔟 j).comap ρ).IsInvertible ∧
        (∃ g : T ⟶ (𝔟 j).blowUp, g ≫ (𝔟 j).blowUpπ = ρ) ∧
        ∃ (E : CartierDivisor T) (hE : E.IsEffective),
          effectiveCartierIdealSheaf E hE = (𝔟 j).comap ρ ∧
          ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0) ∧
      ∃ (G : CartierDivisor T) (hG : G.IsEffective),
        effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ ∧
        (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
          cartierCoefficient G (t : T) = 0) ∧
        (∀ t : T,
          (∀ j, cartierCoefficient G t ≤ cartierCoefficient
            (cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j))) t) ∧
          ∃ j, cartierCoefficient G t = cartierCoefficient
            (cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j))) t) ∧
        (∀ t : T, ∃ (j : J) (g : T.functionFieldˣ), G.IsLocalEquationAt t g ∧
          (cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j))).IsLocalEquationAt t g) ∧
        CartierIsGloballyGenerated (cartierPullback ρ M - G) ∧
        CartierIsNef K (cartierPullback ρ M - G) := by
  obtain ⟨T, _, _, _, _, ρ, _, _, _, _, hρ, cT, r, ξ, hinj, hcoh, hsnc, hTB, _, hA,
      _, haux, _, G, hG, hGI, hG0, hmin, hgen⟩ :=
    exists_projective_snc_model_principalizing_sum c f d D
      (fun i : Fin 0 => i.elim0) (fun j => cartierSectionZeroDivisor M (s j) (hs j))
      (fun j => cartierSectionZeroDivisor_isEffective M (s j) (hs j)) 𝔟 h𝔟
  have hTP : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := ρ) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨hgg, hnef⟩ := hgen M
    (fun j => cartierIsGloballyGenerated_sub_sectionZeroDivisor M (s j) (hs j))
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, hTP, ρ,
    inferInstance, inferInstance, inferInstance, inferInstance, hρ, cT, r, ξ,
    hinj, hcoh, hsnc, hTB, hA, haux, G, hG, hGI, hG0, hmin, ?_, hgg, hnef⟩
  intro t
  exact exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ
    (fun j => cartierSectionZeroDivisor M (s j) (hs j))
    (fun j => cartierSectionZeroDivisor_isEffective M (s j) (hs j)) G hG hGI t

end MixedFujita
