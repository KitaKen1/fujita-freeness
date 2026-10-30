/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.MixedEulerEffectiveCut
public import MixedFujita.CartierMixedIntersection

/-! 通常混合交点数の任意因子における実非被約Cartier切断公式。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Ordinary top intersection with an effective factor is computed on the
actual cut, without assuming that the cut is integral or reduced. -/
theorem proper_cartierMixedIntersection_eq_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H : CartierDivisor X) (hH : H.IsEffective)
    (hdim : topologicalKrullDim X = D.length + 1)
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    cartierMixedIntersection K (H :: D) (by simpa using hdim) =
      cartierPulledModuleMixedEulerDifference K
        (effectiveCartierIdealSheaf H hH).subschemeι
        (SheafOfModules.unit (effectiveCartierIdealSheaf H hH).subscheme.ringCatSheaf) D 0 :=
  proper_cartierMixedEulerDifference_top_eq_effective_cut K D H 0 hH hdim.le


/-- The effective factor may be in ANY position. Symmetry avoids a second
geometric cut argument for each factor. -/
theorem proper_cartierMixedIntersection_eq_effective_cut_at_factor
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (A B : List (CartierDivisor X)) (H : CartierDivisor X) (hH : H.IsEffective)
    (hdim : topologicalKrullDim X = A.length + B.length + 1)
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    cartierMixedIntersection K (A ++ H :: B) (by simpa [add_assoc] using hdim) =
      cartierPulledModuleMixedEulerDifference K
        (effectiveCartierIdealSheaf H hH).subschemeι
        (SheafOfModules.unit (effectiveCartierIdealSheaf H hH).subscheme.ringCatSheaf) (A ++ B) 0 := by
  have hperm : (A ++ H :: B).Perm (H :: (A ++ B)) :=
    List.perm_append_comm.trans (List.perm_append_comm.cons H)
  change cartierMixedEulerDifference K (A ++ H :: B) 0 = _
  rw [cartierMixedEulerDifference_perm K hperm 0]
  exact proper_cartierMixedEulerDifference_top_eq_effective_cut K (A ++ B) H 0 hH
    (by simpa using hdim.le)


/-- When the cut has the expected dimension, the same formula is literally
the ordinary mixed intersection on that actual nonreduced source. -/
theorem proper_cartierMixedIntersection_eq_intersectionOn_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H : CartierDivisor X) (hH : H.IsEffective)
    (hdim : topologicalKrullDim X = D.length + 1)
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))]
    [IsProper ((effectiveCartierIdealSheaf H hH).subscheme ↘ Spec (CommRingCat.of K))]
    (hcut : topologicalKrullDim (effectiveCartierIdealSheaf H hH).subscheme = D.length) :
    cartierMixedIntersection K (H :: D) (by simpa using hdim) =
      cartierMixedIntersectionOn K (effectiveCartierIdealSheaf H hH).subschemeι D hcut :=
  proper_cartierMixedIntersection_eq_effective_cut K D H hH hdim


/-- The ordinary effective-cut formula needs only the original proper
integral scheme and its actual effective Cartier divisor. -/
theorem proper_cartierMixedIntersection_eq_canonical_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H : CartierDivisor X) (hH : H.IsEffective)
    (hdim : topologicalKrullDim X = D.length + 1) :
    let I := effectiveCartierIdealSheaf H hH
    letI : I.subscheme.Over (Spec (CommRingCat.of K)) :=
      ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    cartierMixedIntersection K (H :: D) (by simpa using hdim) =
      cartierPulledModuleMixedEulerDifference K I.subschemeι
        (SheafOfModules.unit I.subscheme.ringCatSheaf) D 0 := by
  let I := effectiveCartierIdealSheaf H hH
  let : I.subscheme.Over (Spec (CommRingCat.of K)) :=
    ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : I.subschemeι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  exact proper_cartierMixedIntersection_eq_effective_cut K D H hH hdim

end MixedFujita
