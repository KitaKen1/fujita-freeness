/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.WholeOpenMixedEulerComparison
public import MixedFujita.MixedEulerCoefficientShift
public import MixedFujita.ModulePushforwardTensorComparisons

/-! 基底開集合の逆像全体の自明化と基底閉支持の消滅段階。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A Cartier twist trivializes over the WHOLE inverse image of a base chart. -/
theorem cartierPulledTensor_exists_base_open_iso
    {X Y : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) (H : CartierDivisor X)
    (M : Y.Modules) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      let W := p ⁻¹ᵁ U
      Nonempty ((Scheme.Modules.pullback W.ι).obj ((cartierPullbackTwistFunctor H p).obj M) ≅
        (Scheme.Modules.pullback W.ι).obj M) := by
  let B := cartierSGALineBundle H
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (B.iSup_eq_top.ge (show x ∈ (⊤ : X.Opens) from trivial))
  let L := B.pullback p
  let W := L.U i
  let a : ((Scheme.Modules.pullback p).obj H.sheaf).restrict W.ι ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor W.ι).mapIso (cartierPulledSheafSGAPowerOneIso H p).symm ≪≫
      L.restrictIso 1 i
  refine ⟨B.U i, hi, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
      ((cartierPullbackTwistFunctor H p).obj M)).symm ≪≫
    (moduleOpenRestrictionTensorIso W.ι ((Scheme.Modules.pullback p).obj H.sheaf) M).symm ≪≫
      tensorIso a (Iso.refl (M.restrict W.ι)) ≪≫ leftUnitor (M.restrict W.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M


/-- One additional base direction vanishes once the preceding mixed difference
vanishes on all coherent modules supported over proper closed base subsets. -/
theorem cartierPulledModuleMixedEulerDifference_cons_vanish_of_lower_base_support
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (H E : CartierDivisor X)
    (hsmall : ∀ T : Set X, IsClosed T → T ≠ Set.univ → ∀ N : Y.Modules, N.IsCoherent →
      CohomologyAux.VanishesOff N (p ⁻¹' T) → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (M : Y.Modules) [M.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p M (H :: D) E = 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := cartierPulledTensor_exists_base_open_iso p H M (genericPoint X)
  have hne : (U : Set X)ᶜ ≠ Set.univ := by
    intro h
    exact (h ▸ Set.mem_univ (genericPoint X) : genericPoint X ∈ (U : Set X)ᶜ) hxU
  let W := p ⁻¹ᵁ U
  have hsmall' : ∀ N : Y.Modules, N.IsCoherent → CohomologyAux.VanishesOff N (W : Set Y)ᶜ →
      cartierPulledModuleMixedEulerDifference K p N D E = 0 := by
    intro N hN hNT
    exact hsmall _ U.2.isClosed_compl hne N hN hNT
  let : ((cartierPullbackTwistFunctor H p).obj M).IsCoherent := cartierPulledTensor_isCoherent H p M
  have h := cartierPulledModuleMixedEulerDifference_eq_of_whole_open_iso K p D E W hsmall'
    M ((cartierPullbackTwistFunctor H p).obj M) e
  rw [cartierPulledModuleMixedEulerDifference_cons_eq_coefficient_difference, h, sub_self]

end MixedFujita
