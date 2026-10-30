/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GenericMixedEulerComparison
public import MixedFujita.MixedEulerCoefficientShift
public import MixedFujita.ModulePushforwardTensorComparisons

/-! 局所自明性と実連接核比較による幾何的支持帰納段階。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Every actual pulled Cartier tensor twist is isomorphic to the coefficient
on an open containing any chosen point, even for a nonintegral source. -/
theorem cartierPulledTensor_exists_open_iso
    {X Y : Scheme.{u}} [IsIntegral X] (p : Y ⟶ X) (H : CartierDivisor X)
    (M : Y.Modules) (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧ Nonempty
      ((Scheme.Modules.pullback W.ι).obj ((cartierPullbackTwistFunctor H p).obj M) ≅
        (Scheme.Modules.pullback W.ι).obj M) := by
  let L := (cartierSGALineBundle H).pullback p
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (L.iSup_eq_top.ge (show y ∈ (⊤ : Y.Opens) from trivial))
  let W := L.U i
  let a : ((Scheme.Modules.pullback p).obj H.sheaf).restrict W.ι ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor W.ι).mapIso (cartierPulledSheafSGAPowerOneIso H p).symm ≪≫
      L.restrictIso 1 i
  refine ⟨W, hi, ⟨?_⟩⟩
  exact ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app
      ((cartierPullbackTwistFunctor H p).obj M)).symm ≪≫
    (moduleOpenRestrictionTensorIso W.ι ((Scheme.Modules.pullback p).obj H.sheaf) M).symm ≪≫
      tensorIso a (Iso.refl (M.restrict W.ι)) ≪≫ leftUnitor (M.restrict W.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M


/-- Lower-support vanishing makes a locally trivial Cartier twist invisible
to the actual mixed Euler coefficient, with the comparison built internally. -/
theorem cartierPulledModuleMixedEulerDifference_twist_eq_of_lower_support
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (H E : CartierDivisor X) (y : Y)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (M : Y.Modules) [M.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p ((cartierPullbackTwistFunctor H p).obj M) D E =
      cartierPulledModuleMixedEulerDifference K p M D E := by
  let : ((cartierPullbackTwistFunctor H p).obj M).IsCoherent := cartierPulledTensor_isCoherent H p M
  obtain ⟨W, hyW, ⟨e⟩⟩ := cartierPulledTensor_exists_open_iso p H M y
  exact (cartierPulledModuleMixedEulerDifference_eq_of_open_iso K p D E hsmall
    M ((cartierPullbackTwistFunctor H p).obj M) W ⟨y, hyW⟩ e).symm


/-- The geometric support-induction step: vanishing of the current mixed
coefficient on proper closed supports kills one additional Cartier difference
on every coherent module. No denominator ideal, common module, local frame,
comparison map, exact sequence or Euler identity is supplied. -/
theorem cartierPulledModuleMixedEulerDifference_cons_vanish_of_lower_support
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (H E : CartierDivisor X) (y : Y)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (M : Y.Modules) [M.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p M (H :: D) E = 0 := by
  rw [cartierPulledModuleMixedEulerDifference_cons_eq_coefficient_difference,
    cartierPulledModuleMixedEulerDifference_twist_eq_of_lower_support K p D H E y hsmall M,
    sub_self]

end MixedFujita
