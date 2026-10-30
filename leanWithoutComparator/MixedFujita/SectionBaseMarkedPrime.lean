/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBaseIdeal
public import MixedFujita.BlowUpLiftPoints
public import MixedFujita.LocalBirationalOrders
public import MixedFujita.SmoothProperCurveSections
public import MixedFujita.BirationalComposition

/-!
Retain a prescribed DVR prime on a blow-up when principalizing a section base ideal. The actual
stalk isomorphism preserves every pulled-back section coefficient, hence the fixed-part
coefficient. A nonzero such coefficient forces the prime into the model's marked SNC family.
The numerical discrepancy of the original point blow-up and the strict inequalities at the
other components are separate obligations.
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
variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
  [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian T]
  [Smooth (T ↘ Spec (CommRingCat.of K))] {J : Type*} [Finite J]

omit [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] in
theorem sectionBase_blowUp_isLocallyNoetherian (I : X.IdealSheafData) :
    IsLocallyNoetherian I.blowUp := by
  have : IsProper I.blowUpπ := Scheme.IdealSheafData.blowUp.isProper_π I
  exact LocallyOfFiniteType.isLocallyNoetherian I.blowUpπ

attribute [local instance] sectionBase_blowUp_isLocallyNoetherian

/-- The marked prime and the actual coefficient of the principalized section ideal survive. -/
theorem principalized_sectionBase_exists_prime_over_blowUp
    (I : X.IdealSheafData) [IsIntegral I.blowUp] [IsDominant I.blowUpπ]
    (hη : genericPoint X ∉ (I.support : Set X))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom)
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ)
    (b : I.blowUp) [IsDiscreteValuationRing (I.blowUp.presheaf.stalk b)]
    (hb : Order.coheight b = 1) (M : CartierDivisor X)
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ)
    (m : ℤ) (hm : ∀ j,
      cartierCoefficient (cartierPullback I.blowUpπ
        (cartierSectionZeroDivisor M (s j) (hs j))) b = m) :
    ∃ t : CodimensionOnePoint T, g (t : T) = b ∧
      Function.Bijective (g.stalkMap (t : T)) ∧ cartierCoefficient G (t : T) = m := by
  have hgdom : IsDominant g := blowUp_lift_isDominant I hη ρ g hg
  obtain ⟨t, ht, hbij, hcod⟩ := blowUp_lift_exists_codimensionOne_over I hη ρ hρ g hg b hb
  let p : CodimensionOnePoint T := ⟨t, hcod⟩
  have hBcod : Order.coheight (g t) = 1 := ht ▸ hb
  have hBdvr : IsDiscreteValuationRing (I.blowUp.presheaf.stalk (g t)) := ht ▸ inferInstance
  have hTdvr : IsDiscreteValuationRing (T.presheaf.stalk t) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) p
  have hcoef (j : J) : cartierCoefficient
      (cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j))) t = m := by
    have heq : cartierPullback ρ (cartierSectionZeroDivisor M (s j) (hs j)) =
        cartierPullback (g ≫ I.blowUpπ) (cartierSectionZeroDivisor M (s j) (hs j)) := by
      congr 1
      exact hg.symm
    rw [heq, cartierPullback_comp]
    rw [cartierCoefficient_pullback_of_stalkMap_bijective g p hBcod hbij, ht]
    exact hm j
  obtain ⟨j, hj⟩ := (cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
    ρ (fun j => cartierSectionZeroDivisor M (s j) (hs j))
    (fun j => cartierSectionZeroDivisor_isEffective M (s j) (hs j)) G hG hGI t).2
  exact ⟨p, ht, hbij, hj.trans (hcoef j)⟩

/-- A nonzero retained coefficient gives an actual index in the marked SNC family. -/
theorem principalized_sectionBase_exists_marked_component
    (I : X.IdealSheafData) [IsIntegral I.blowUp] [IsDominant I.blowUpπ]
    (hη : genericPoint X ∉ (I.support : Set X))
    (ρ : T ⟶ X) [IsDominant ρ] [IsProper ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Surjective (dominantFunctionFieldMap ρ).hom)
    (g : T ⟶ I.blowUp) (hg : g ≫ I.blowUpπ = ρ)
    (b : I.blowUp) [IsDiscreteValuationRing (I.blowUp.presheaf.stalk b)]
    (hb : Order.coheight b = 1) (M : CartierDivisor X)
    (s : J → Γ(M.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal M s hs).comap ρ)
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ j,
      cartierCoefficient (cartierPullback I.blowUpπ
        (cartierSectionZeroDivisor M (s j) (hs j))) b = m)
    {r : ℕ} (ξ : Fin r → T)
    (hG0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0) :
    ∃ k : Fin r, g (ξ k) = b ∧ ρ (ξ k) = I.blowUpπ b ∧ cartierCoefficient G (ξ k) = m := by
  obtain ⟨t, ht, _, hcoef⟩ := principalized_sectionBase_exists_prime_over_blowUp (K := K)
    I hη ρ hρ g hg b hb M s hs G hG hGI m hm
  have hmem : (t : T) ∈ Set.range ξ := by
    by_contra hnot
    exact hm0 (hcoef.symm.trans (hG0 t hnot))
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, by simpa only [hk] using ht, ?_, by simpa only [hk] using hcoef⟩
  have he := congrArg (fun f : T ⟶ X => f (t : T)) hg
  simpa only [Scheme.Hom.comp_apply, ht, hk] using he.symm

end MixedFujita
