/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperZeroDimensionalEulerPositive
public import MixedFujita.CoherentMixedEulerPositivityReduction
public import MixedFujita.SemiampleCoherentMixedEulerNonnegative

/-! 零次元を含むsemiample混合係数の実正値閉商からの正値性。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- One actual positive integral closed quotient suffices in every
arity, including zero-dimensional nonreduced cuts and empty direction lists. -/
theorem proper_semiample_unit_mixed_positive_of_closed_quotient
    (K : Type u) [Field K] {X Y T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [Y.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X))
    (hdim : topologicalKrullDim Y ≤ D.length)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (i : T ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (hpos : 0 < cartierPulledModuleMixedEulerDifference K (i ≫ p)
      (CohomologyAux.unitModule T) D 0) :
    0 < cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D 0 := by
  cases D with
  | nil =>
    rw [cartierPulledModuleMixedEulerDifference_empty_zero_unit]
    exact proper_zeroDimensional_unitEulerChar_positive K hdim (Nonempty.map i inferInstance)
  | cons H D =>
    apply proper_cartierPulledModuleMixedEulerDifference_top_unit_positive_of_closed_quotient
      K D.length hdim p (H :: D) (by simp) 0 ?_ i hpos
    intro Z _ _ _ j _ _
    exact proper_semiample_coherentMixedEuler_nonneg K (D.length + 1)
      (j.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim) (j ≫ p)
      (H :: D) rfl hD (CohomologyAux.unitModule Z) 0

end MixedFujita
