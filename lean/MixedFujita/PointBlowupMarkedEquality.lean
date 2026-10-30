/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionMappedPointOrder
public import MixedFujita.SectionBaseMarkedDiscrepancy
public import MixedFujita.PointBlowupGeometricDiscrepancy
public import MixedFujita.BirationalValuationFibre

/-! On an actual proper birational model principalizing the supplied
section base ideal and dominating the actual point blow-up, construct a
marked prime with fixed coefficient nh and discrepancy coefficient n-1.
The point-blow-up DVR, both coefficient values, its unique lifted point and
the final threshold equality are outputs. No threshold or adjunction input is used. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 1000000 in
theorem smooth_closedPoint_principalized_sectionBase_marked_equality {J : Type*} [Finite J]
    (hn : topologicalKrullDim X = n) (hn1 : 1 ≤ n) (x : X) (hx : IsClosed ({x} : Set X))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (g : T ⟶ (pointClosureIdeal x).blowUp) (hg : g ≫ (pointClosureIdeal x).blowUpπ = ρ)
    (c₀ : EtaleChart K X n) (cT : EtaleChart K T n) (M : CartierDivisor X)
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0) (h : ℕ) (hh : 0 < h)
    (horders : ∀ j, cartierSectionVanishingOrder M x (s j) = ((n * h : ℕ) : ℕ∞))
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ)
    {r : ℕ} (ξ : Fin r → T)
    (hG0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) :
    ∃ k : Fin r, ρ (ξ k) = x ∧ Order.coheight (g (ξ k)) = 1 ∧
      Function.Bijective (g.stalkMap (ξ k)) ∧
      (∀ t : T, g t = g (ξ k) → t = ξ k) ∧
      cartierCoefficient G (ξ k) = ((n * h : ℕ) : ℤ) ∧
      cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
        cT etaleCharts_cover) (ξ k) = (n : ℤ) - 1 ∧
      cartierCoefficient G (ξ k) = (h : ℤ) *
        (1 + cartierCoefficient (logDiscrepancyDivisor n ρ hρ c₀ 1 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
          cT etaleCharts_cover) (ξ k)) := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let : Smooth (T ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnpos : 0 < n := by omega
  have hdim : 0 < topologicalKrullDim X := by rw [hn]; exact_mod_cast hnpos
  let I := pointClosureIdeal x
  let : IsIntegral I.blowUp := pointBlowup_isIntegral hdim x hx
  let : IsDominant I.blowUpπ := pointBlowup_isDominant hdim x hx
  let : IsLocallyNoetherian I.blowUp := Scheme.IdealSheafData.blowUp.isLocallyNoetherian I
  let : I.blowUp.Over (Spec (.of K)) := ⟨I.blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let : I.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension n (I.blowUp ↘ Spec (.of K)) :=
    smooth_closedPoint_pointBlowup_smoothOfRelativeDimension hn x hx
  let : g.IsOver (Spec (.of K)) := ⟨by
    change g ≫ (I.blowUpπ ≫ (X ↘ Spec (.of K))) = T ↘ Spec (.of K)
    rw [← Category.assoc, hg]
    exact HomIsOver.comp_over (f := ρ) (S := Spec (.of K))⟩
  have hη : genericPoint X ∉ (I.support : Set X) := pointClosureIdeal_genericPoint_notMem hdim x hx
  have : IsDominant g := blowUp_lift_isDominant I hη ρ g hg
  have : IsProper I.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π I
  have : IsProper g := by
    have : IsProper (g ≫ I.blowUpπ) := by rw [hg]; infer_instance
    exact IsProper.of_comp g I.blowUpπ
  have hgfield : Function.Bijective (dominantFunctionFieldMap g).hom :=
    ⟨(dominantFunctionFieldMap g).hom.injective,
      lift_functionFieldMap_surjective I.blowUpπ ρ hρ.2 g hg⟩
  have hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) I.blowUpπ) :=
    pointBlowup_functionField_bijective hdim x hx
  obtain ⟨cY, _⟩ := Opens.mem_iSup.mp
    ((etaleCharts_cover (K := K) (X := I.blowUp) (n := n)).symm ▸ Opens.mem_top (genericPoint I.blowUp))
  obtain ⟨b, hb, hDVR, hcan, _, horder⟩ :=
    smooth_closedPoint_pointBlowup_exists_dvr_orders_and_discrepancy hn x hx ⟨0, hnpos⟩ c₀ cY
  let := hDVR
  obtain ⟨fM, hfM⟩ := M.exists_isLocalEquationAt x
  have hm (j : J) : cartierCoefficient (cartierPullback I.blowUpπ
      (cartierSectionZeroDivisor M (s j) (hs j))) (b : I.blowUp) = ((n * h : ℕ) : ℤ) :=
    cartierPullback_sectionZeroDivisor_coefficient_of_mappedPoint_order I.blowUpπ b x hb
      M fM hfM (s j) (hs j) (n * h) (horder M fM hfM (s j) (n * h) (horders j))
  have hm0 : ((n * h : ℕ) : ℤ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hnpos.ne' hh.ne'
  have hdisc : cartierCoefficient (logDiscrepancyDivisor n I.blowUpπ hπ c₀ 1 1
      (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0)
      cY etaleCharts_cover) (b : I.blowUp) = (n : ℤ) - 1 := by
    rw [add_zero, logDiscrepancyDivisor_boundary_zero, one_smul]
    exact hcan
  obtain ⟨k, hkg, hkbij, hkx, hkG, hkdisc⟩ := principalized_sectionBase_exists_marked_discrepancy (K := K)
    I hη hπ ρ hρ g hg b M s hs G hG hGI ((n * h : ℕ) : ℤ) hm0 hm c₀ 1 1
    (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X 1) + 0) cY cT ξ hG0
  have hkD := hkdisc.trans hdisc
  have hkuniq (t : T) (ht : g t = g (ξ k)) : t = ξ k :=
    eq_of_birational_over_smooth_prime (K := K) (n := n) g hgfield b t (ξ k)
      (ht.trans hkg) hkg
  refine ⟨k, hkx.trans hb, by rw [hkg]; exact b.property, hkbij, hkuniq, hkG, hkD, ?_⟩
  rw [hkG, hkD]
  push_cast
  ring

end MixedFujita
