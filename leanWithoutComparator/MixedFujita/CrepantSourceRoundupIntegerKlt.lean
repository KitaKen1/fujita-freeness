/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCRoundupIntegerKlt
public import MixedFujita.CrepantKltDescent
public import MixedFujita.ThresholdModelLifting

/-!
Retain the original crepant SNC model and its actual roundup, but allow an
arbitrary effective perturbing Cartier divisor on that model itself. In
particular the perturbation need not descend from the original variety.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The original actual crepant boundary is the identity-model boundary of
the crepant source pair, with the source form and divisor transported exactly. -/
theorem crepantBoundaryCartier_eq_identity_crepant_source
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ)
    (D : CartierDivisor X) (cT : EtaleChart K T n) :
    crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover =
      crepantBoundaryCartier (𝟙 T) (dominantFunctionFieldMap_id_bijective (X := T)) cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D) cT etaleCharts_cover := by
  simpa only [Category.id_comp] using crepantBoundaryCartier_comp ρ (𝟙 T) hρ
    (dominantFunctionFieldMap_id_bijective (X := T)) c f d D cT cT etaleCharts_cover

/-- An effective divisor on the existing source model has the exact integer
klt/roundup criterion without a descent or joint SNC support premise. -/
theorem crepant_source_roundup_sub_integer_isEffective_iff_klt
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (G : CartierDivisor T) (hG : G.IsEffective) (p : ℕ) :
    (E - p • G).IsEffective ↔ LogPairIsKlt cT (crepantPullbackFormUnit ρ hρ c f cT) d
      (cartierPullback ρ D + (d * p) • G) := by
  have hb := crepantBoundaryCartier_eq_identity_crepant_source ρ hρ c f d D cT
  have hs : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier (𝟙 T)
        (dominantFunctionFieldMap_id_bijective (X := T)) cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D)
        cT etaleCharts_cover) (t : T) = 0 := by
    simpa only [← hb] using hsupport
  have he : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (𝟙 T)
        (dominantFunctionFieldMap_id_bijective (X := T)) cT
        (crepantPullbackFormUnit ρ hρ c f cT) d (cartierPullback ρ D)
        cT etaleCharts_cover) (t : T) : ℝ) / (d : ℝ))⌉ := by
    simpa only [← hb] using hE
  simpa only [cartierPullback_id] using
    snc_roundup_sub_integer_pullback_isEffective_iff_klt (𝟙 T)
      (dominantFunctionFieldMap_id_bijective (X := T)) hnormT cT
      (crepantPullbackFormUnit ρ hρ c f cT) d hd (cartierPullback ρ D) G hG cT
      ξ hinj hξ hsnc hs E he p

/-- The same criterion for the actual distinguished rational unit section on
the original source model, including perturbations which do not descend. -/
theorem crepant_source_roundup_integer_unit_section_iff_klt
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    (G : CartierDivisor T) (hG : G.IsEffective) (p : ℕ) :
    Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ⊤
      (1 : Γ(T, (⊤ : T.Opens))) ∈ (E - p • G).sections ⊤ ↔
      LogPairIsKlt cT (crepantPullbackFormUnit ρ hρ c f cT) d
        (cartierPullback ρ D + (d * p) • G) :=
  CartierDivisor.isEffective_iff_one_mem_sections.symm.trans
    (crepant_source_roundup_sub_integer_isEffective_iff_klt ρ hρ hnormT c f d hd D cT
      ξ hinj hξ hsnc hsupport E hE G hG p)

end MixedFujita
