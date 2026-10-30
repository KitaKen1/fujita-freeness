/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EmptySourceMixedEulerDifference
public import MixedFujita.HyperplanePowerMixedEulerDegree
public import MixedFujita.AmpleMixedIntersectionCut

/-! 実射影冪表示の正の有効倍数切断の非空性。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A positive diagonal coefficient forces every actual effective
representative of a positive multiple to have a nonempty cut. -/
theorem proper_hyperplanePower_effective_multiple_cut_nonempty
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (d : ℕ) (hdim : topologicalKrullDim X = (d + 1 : ℕ))
    (H : CartierDivisor X) (hH : CartierHasHyperplanePower K H)
    (G : CartierDivisor X) (hG : G.IsEffective) (q : ℕ) (hq : 0 < q)
    (a : (q • H).sheaf ≅ G.sheaf) :
    Nonempty (effectiveCartierIdealSheaf G hG).subscheme := by
  by_contra hempty
  let : IsEmpty (effectiveCartierIdealSheaf G hG).subscheme := not_nonempty_iff.mp hempty
  let I := effectiveCartierIdealSheaf G hG
  let : I.subscheme.Over (Spec (CommRingCat.of K)) := ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  have hpos := proper_hyperplanePower_mixedEuler_diagonal_positive K (d + 1) hdim (by omega) H hH
  have hcut := proper_cartierMixedIntersection_scaled_effective_cut K
    (List.replicate d H) H G hG q a (by simpa [List.length_replicate] using hdim)
  have hz := cartierPulledModuleMixedEulerDifference_empty_source K I.subschemeι
    (CohomologyAux.unitModule I.subscheme) (List.replicate d H) 0
  change (q : ℤ) * cartierMixedEulerDifference K (List.replicate (d + 1) H) 0 =
    cartierPulledModuleMixedEulerDifference K I.subschemeι
      (CohomologyAux.unitModule I.subscheme) (List.replicate d H) 0 at hcut
  rw [hz] at hcut
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  exact (ne_of_gt (mul_pos hq' hpos)) hcut

end MixedFujita
