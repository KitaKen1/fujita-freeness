/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperSurjectiveComponentImage

/-! 実引き戻し切断から期待次元の基底を支配する整成分を内部構成。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- An actual component of a pulled-back effective cut dominates an
actual integral closed base of dimension one less. All witnesses are
constructed from the original proper dominant map and nonempty base cut. -/
theorem proper_effectiveCut_exists_dominating_expected_component
    (K : Type u) [Field K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (p : X ⟶ B) [IsProper p] [IsDominant p]
    (n d : ℕ) (hX : topologicalKrullDim X = (n + 1 : ℕ))
    (hB : topologicalKrullDim B = (d + 1 : ℕ))
    (G : CartierDivisor B) (hG : G.IsEffective)
    (hne : Nonempty (effectiveCartierIdealSheaf G hG).subscheme) :
    ∃ (T C : Scheme.{u})
      (i : T ⟶ (effectiveCartierIdealSheaf (cartierPullback p G)
        (cartierPullback_isEffective p G hG)).subscheme)
      (j : C ⟶ B) (r : T ⟶ C),
      IsIntegral T ∧ IsIntegral C ∧ IsClosedImmersion i ∧ IsClosedImmersion j ∧
      IsDominant r ∧ topologicalKrullDim T = n ∧ topologicalKrullDim C = d ∧
      r ≫ j = i ≫ (effectiveCartierIdealSheaf (cartierPullback p G)
        (cartierPullback_isEffective p G hG)).subschemeι ≫ p := by
  let I := effectiveCartierIdealSheaf (cartierPullback p G) (cartierPullback_isEffective p G hG)
  let J := effectiveCartierIdealSheaf G hG
  obtain ⟨q, hq, hsurj, hfac⟩ := proper_surjective_idealCut_map p
    (surjective_of_isProper_of_isDominant p) I J (effectiveCartierIdealSheaf_cartierPullback p G hG)
  let := hq
  let z := Classical.choice hne
  let Z := irreducibleComponent z
  have hZ : Z ∈ irreducibleComponents J.subscheme := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨A, hA, himage⟩ := proper_surjective_exists_component_image q hsurj Z hZ
  obtain ⟨T, i, hT, hi, hrange, hdimT⟩ :=
    effectiveCartierCut_component_exists_integral_expected_dimension K n hX
      (cartierPullback p G) (cartierPullback_isEffective p G hG) A hA
  let := hT
  let := hi
  obtain ⟨S, k, hS, hk, hrangeS, hdimS⟩ :=
    effectiveCartierCut_component_exists_integral_expected_dimension K d hB G hG Z hZ
  let := hS
  let := hk
  let : T.Over (Spec (CommRingCat.of K)) := ⟨i ≫ I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := T)
  let f : T ⟶ B := i ≫ I.subschemeι ≫ p
  let : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  let C := f.image
  have hC : IsIntegral C := OAI.NumericalDimensionOne.integral_image f
  have hr : Set.range f = Set.range (k ≫ J.subschemeι) := by
    have hf : f = (i ≫ q) ≫ J.subschemeι := by dsimp [f]; rw [Category.assoc, hfac]
    rw [hf]
    have hfq : Set.range (i ≫ q) = Z := by
      change Set.range ((q : _ → _) ∘ (i : _ → _)) = Z
      rw [Set.range_comp, hrange, himage]
    change Set.range ((J.subschemeι : _ → _) ∘ (i ≫ q : _ → _)) =
      Set.range ((J.subschemeι : _ → _) ∘ (k : _ → _))
    rw [Set.range_comp, Set.range_comp, hfq, hrangeS]
  have hclosed : IsClosed (Set.range f) := by
    rw [hr]
    exact (k ≫ J.subschemeι).isClosedEmbedding.isClosed_range
  have himagerange : Set.range f.imageι = Set.range (k ≫ J.subschemeι) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker, hclosed.closure_eq, hr]
  have hdimC : topologicalKrullDim C = d :=
    (closedImmersion_dimension_eq_of_range_eq f.imageι (k ≫ J.subschemeι) himagerange).trans hdimS
  exact ⟨T, C, i, f.imageι, f.toImage, hT, hC, hi, inferInstance,
    inferInstance, hdimT, hdimC, f.toImage_imageι⟩

end MixedFujita
