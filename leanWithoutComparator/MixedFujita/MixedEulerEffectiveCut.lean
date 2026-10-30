/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutDimension
public import MixedFujita.ProperCartierMixedEulerCut
public import MixedFujita.MixedForwardDifferenceComposition
public import MixedFujita.TopDimensionalMixedEuler

/-! 任意混合差分の実Cartier切断公式・最高次捻り消去と標準体構造。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- One effective factor of ANY actual mixed Euler difference is exactly
the remaining mixed difference on the actual Cartier subscheme. The cut
retains every nilpotent layer and may be reducible. -/
theorem proper_cartierMixedEulerDifference_cons_eq_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) (hH : H.IsEffective)
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    cartierMixedEulerDifference K (H :: D) E =
      cartierPulledModuleMixedEulerDifference K
        (effectiveCartierIdealSheaf H hH).subschemeι
        (SheafOfModules.unit (effectiveCartierIdealSheaf H hH).subscheme.ringCatSheaf)
        D (E + H) := by
  let I := effectiveCartierIdealSheaf H hH
  let p := I.subschemeι
  let O : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  let f : CartierDivisor X → ℤ := fun F =>
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) F.sheaf
  let g : CartierDivisor X → ℤ := fun F =>
    Scheme.Modules.eulerChar (I.subscheme ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor F p).obj O)
  have heq : fwdDiff H f = fun F => g (F + H) := by
    funext F
    have h := proper_cartierMixedEulerDifference_singleton_eq_cut_eulerChar K H F hH
    exact h.trans (moduleEulerChar_congr K
      (rightUnitor ((Scheme.Modules.pullback p).obj (F + H).sheaf)).symm)
  change mixedForwardDifference (H :: D) f E = mixedForwardDifference D g (E + H)
  rw [← mixedForwardDifference_right_singleton D H f, heq]
  exact mixedForwardDifference_comp_add D g H E


/-- In top dimension, the effective-cut formula has no residual base twist:
the actual geometric dimension drop proves the required independence. -/
theorem proper_cartierMixedEulerDifference_top_eq_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) (hH : H.IsEffective)
    (hdim : topologicalKrullDim X ≤ (D.length + 1 : ℕ))
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    cartierMixedEulerDifference K (H :: D) E =
      cartierPulledModuleMixedEulerDifference K
        (effectiveCartierIdealSheaf H hH).subschemeι
        (SheafOfModules.unit (effectiveCartierIdealSheaf H hH).subscheme.ringCatSheaf) D 0 := by
  let I := effectiveCartierIdealSheaf H hH
  let p := I.subschemeι
  let O : I.subscheme.Modules := SheafOfModules.unit I.subscheme.ringCatSheaf
  let : O.IsCoherent := invertible_module_isCoherent (X := I.subscheme) O
  let : IsProper (I.subscheme ↘ Spec (CommRingCat.of K)) := by
    have heq : p ≫ (X ↘ Spec (CommRingCat.of K)) = I.subscheme ↘ Spec (CommRingCat.of K) :=
      HomIsOver.comp_over
    rw [← heq]
    infer_instance
  exact (proper_cartierMixedEulerDifference_cons_eq_effective_cut K D H E hH).trans
    (proper_cartierPulledModuleMixedEulerDifference_top_base_independent K D.length
      (effectiveCartierCut_topologicalKrullDim_le H hH D.length hdim) p O D rfl (E + H) 0)


/-- The cut formula with its canonical structure over K constructed
internally; no structure on the Cartier subscheme is an input. -/
theorem proper_cartierMixedEulerDifference_cons_eq_canonical_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H E : CartierDivisor X) (hH : H.IsEffective) :
    let I := effectiveCartierIdealSheaf H hH
    letI : I.subscheme.Over (Spec (CommRingCat.of K)) :=
      ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    cartierMixedEulerDifference K (H :: D) E =
      cartierPulledModuleMixedEulerDifference K I.subschemeι
        (SheafOfModules.unit I.subscheme.ringCatSheaf) D (E + H) := by
  let I := effectiveCartierIdealSheaf H hH
  let : I.subscheme.Over (Spec (CommRingCat.of K)) :=
    ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  exact proper_cartierMixedEulerDifference_cons_eq_effective_cut K D H E hH

end MixedFujita
