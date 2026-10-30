/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveCartierCutPureDimension
public import MixedFujita.ProperZeroDimensionalEulerPositive
public import MixedFujita.SemiampleCartierMixedIntersection

/-! 非空の実有効Cartier切断と元ample因子の厳密混合正値性。 See reports/check-230-effective-cut-low-iitaka-dictionary.json for the verified scope. Equality for 2 <= kappa < dimension, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A NONEMPTY actual effective Cartier cut has positive ample mixed
unit coefficient. Its integral quotient, expected dimension and
nonnegative coherent kernel are all constructed internally. -/
theorem proper_effective_nonempty_ample_cartierMixedEuler_positive
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = (n + 1 : ℕ))
    (G : CartierDivisor X) (hG : G.IsEffective)
    (hne : Nonempty (effectiveCartierIdealSheaf G hG).subscheme)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) (E : CartierDivisor X) :
    0 < cartierMixedEulerDifference K (G :: D) E := by
  let I := effectiveCartierIdealSheaf G hG
  let Y := I.subscheme
  let p : Y ⟶ X := I.subschemeι
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (p ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let O : Y.Modules := CohomologyAux.unitModule Y
  let : O.IsCoherent := invertible_module_isCoherent O
  have hdimY : topologicalKrullDim Y ≤ n := effectiveCartierCut_topologicalKrullDim_le G hG n hdim.le
  rw [proper_cartierMixedEulerDifference_top_eq_effective_cut K D G E hG
    (by simpa [hlen] using hdim.le)]
  cases n with
  | zero =>
    have hnil : D = [] := List.eq_nil_of_length_eq_zero hlen
    subst D
    rw [cartierPulledModuleMixedEulerDifference_empty_zero_unit]
    exact proper_zeroDimensional_unitEulerChar_positive K hdimY hne
  | succ m =>
    obtain ⟨T, i, hT, hi, hdimT⟩ :=
      effectiveCartierCut_nonempty_exists_integral_expected_dimension K (m + 1) hdim G hG hne
    let := hT
    let := hi
    let : T.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
    let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
      change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
      infer_instance
    have hunit : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
        [IsProper (Z ↘ Spec (CommRingCat.of K))]
        (j : Z ⟶ Y) [IsClosedImmersion j] [j.IsOver (Spec (CommRingCat.of K))],
        0 ≤ cartierPulledModuleMixedEulerDifference K (j ≫ p) (CohomologyAux.unitModule Z) D 0 := by
      intro Z _ _ _ j _ _
      let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
      exact proper_pulled_ample_coherentMixedEuler_nonneg K (m + 1)
        (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdimY) (j ≫ p) D hlen hD _ 0
    have hpos : 0 < cartierPulledModuleMixedEulerDifference K (i ≫ p)
        (CohomologyAux.unitModule T) D 0 := by
      obtain ⟨F, hFlen, hF, hval⟩ := closed_hyperplanePowers_exists_representatives K (i ≫ p) D
        (fun H hH => cartierHasHyperplanePower_of_isAmpleProj K H (hD H hH))
      rw [hval]
      exact proper_hyperplanePowers_mixedEuler_positive K m T hdimT F (hFlen.trans hlen) hF
    exact proper_cartierPulledModuleMixedEulerDifference_top_unit_positive_of_closed_quotient
      K m hdimY p D (by omega) 0 hunit i hpos

end MixedFujita
