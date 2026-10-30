/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SectionBaseMarkedPrime
public import MixedFujita.DiscrepancyPrimeComparison

/-! The retained prime of a principalized section base ideal preserves
both the fixed-part coefficient and the actual discrepancy coefficient
on the same model and at the same marked point. Its stalk isomorphism,
codimension and membership in the marked family are constructed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra sectionBase_blowUp_isLocallyNoetherian
variable {K : Type u} [Field K] {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))] {n : ℕ}
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]

theorem principalized_sectionBase_exists_marked_discrepancy {J : Type*} [Finite J]
    (I : X.IdealSheafData) [IsIntegral I.blowUp] [IsDominant I.blowUpπ]
    [I.blowUp.Over (Spec (.of K))] [I.blowUpπ.IsOver (Spec (.of K))]
    [SmoothOfRelativeDimension n (I.blowUp ↘ Spec (.of K))]
    (hη : genericPoint X ∉ (I.support : Set X))
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) I.blowUpπ))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ) [g.IsOver (Spec (.of K))]
    (b : CodimensionOnePoint I.blowUp) (M : CartierDivisor X)
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ)
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ j,
      cartierCoefficient (cartierPullback I.blowUpπ
        (cartierSectionZeroDivisor M (s j) (hs j))) (b : I.blowUp) = m)
    (c₀ : EtaleChart K X n) (f₀ : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (cY : EtaleChart K I.blowUp n) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T)
    (hG0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) :
    ∃ k : Fin r, g (ξ k) = (b : I.blowUp) ∧ Function.Bijective (g.stalkMap (ξ k)) ∧
      ρ (ξ k) = I.blowUpπ (b : I.blowUp) ∧
      cartierCoefficient G (ξ k) = m ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ f₀ d D cT etaleCharts_cover) (ξ k) =
        cartierCoefficient (logDiscrepancyDivisor n I.blowUpπ hπ c₀ f₀ d D cY etaleCharts_cover)
          (b : I.blowUp) := by
  let : Smooth (T ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (I.blowUp ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let := smoothOverField_codimensionOne_stalk_DVR (K := K) b
  let : IsDominant g := blowUp_lift_isDominant I hη ρ g hg
  have hgsurj : Function.Surjective (dominantFunctionFieldMap g).hom :=
    lift_functionFieldMap_surjective I.blowUpπ ρ hρ.2 g hg
  have hgbij : Function.Bijective (dominantFunctionFieldAlgHom (K := K) g) :=
    ⟨(dominantFunctionFieldAlgHom (K := K) g).injective, hgsurj⟩
  obtain ⟨t, ht, htbij, hcoef⟩ := principalized_sectionBase_exists_prime_over_blowUp (K := K)
    I hη ρ hρ.2 g hg (b : I.blowUp) b.property M s hs G hG hGI m hm
  have hcod : Order.coheight (g (t : T)) = 1 := ht ▸ b.property
  have hdisc := logDiscrepancyDivisor_comp_coefficient_of_stalkMap_bijective
    I.blowUpπ g hπ hgbij c₀ f₀ d D cY cT t hcod htbij
  have hdisc' : cartierCoefficient
      (logDiscrepancyDivisor n ρ hρ c₀ f₀ d D cT etaleCharts_cover) (t : T) =
        cartierCoefficient (logDiscrepancyDivisor n I.blowUpπ hπ c₀ f₀ d D cY etaleCharts_cover)
          (b : I.blowUp) := by
    simpa only [hg, ht] using hdisc
  have hmem : (t : T) ∈ Set.range ξ := by
    by_contra hn
    exact hm0 (hcoef.symm.trans (hG0 t hn))
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, by simpa only [hk] using ht, by rw [hk]; exact htbij, ?_, by simpa only [hk] using hcoef,
    by simpa only [hk] using hdisc'⟩
  have he := congrArg (fun f : T ⟶ X => f (t : T)) hg
  simpa only [Scheme.Hom.comp_apply, ht, hk] using he.symm

end MixedFujita
