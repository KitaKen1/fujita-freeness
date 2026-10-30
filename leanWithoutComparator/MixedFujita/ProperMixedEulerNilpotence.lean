/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedEulerSupportStep
public import MixedFujita.ProperClosedImmersionDimension
public import MixedFujita.CoherentMixedEulerClosedSupport
public import MixedFujita.ZeroDimensionalCoherentMixedEuler

/-! 全次元proper非被約源・任意連接係数の幾何次元超過混合差分消滅。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Geometric dimension bounds the order of every actual mixed Euler
difference on a proper scheme, with arbitrary coherent coefficients and no
integrality or reducedness assumption on the source. -/
theorem proper_cartierPulledModuleMixedEulerDifference_vanish_of_length
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (p : Y ⟶ X)
    (M : Y.Modules) [M.IsCoherent] (D : List (CartierDivisor X))
    (hlen : n < D.length) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  induction n generalizing Y D with
  | zero =>
    apply cartierPulledModuleMixedEulerDifference_vanish_of_pulled_integral_step K p D E ?_ M
    intro Z _ _ _ i _ _ hsmall G hG
    have hle : topologicalKrullDim Z ≤ 0 :=
      i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    have hge : (0 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
      let : Nonempty (IrreducibleCloseds Z) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg
    cases D with
    | nil => simp at hlen
    | cons H D =>
      exact zeroDimensional_integral_cartierPulledModuleMixedEulerDifference_vanishes
        K (le_antisymm hle hge) (i ≫ p) G D H E
  | succ n ih =>
    apply cartierPulledModuleMixedEulerDifference_vanish_of_pulled_integral_step K p D E ?_ M
    intro Z _ _ _ i _ _ hsmall G hG
    let := hG
    have hdimZ : topologicalKrullDim Z ≤ (n + 1 : ℕ) :=
      i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    cases D with
    | nil => simp at hlen
    | cons H D =>
      apply cartierPulledModuleMixedEulerDifference_cons_vanish_of_lower_support
        K (i ≫ p) D H E (genericPoint Z) ?_ G
      intro N hN T hT hTne hNT
      let J : Z.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩
      let j := J.subschemeι
      have hjrange : Set.range j = T := by
        change Set.range J.subschemeι = T
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      let : J.subscheme.Over (Spec (CommRingCat.of K)) :=
        ⟨j ≫ (Z ↘ Spec (CommRingCat.of K))⟩
      let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      let : IsProper (J.subscheme ↘ Spec (CommRingCat.of K)) := by
        change IsProper (j ≫ (Z ↘ Spec (CommRingCat.of K)))
        infer_instance
      have hdimJ : topologicalKrullDim J.subscheme ≤ n :=
        properClosedImmersion_topologicalKrullDim_le_predecessor j
          (by rw [hjrange]; exact hTne) n hdimZ
      let := hN
      apply cartierPulledModuleMixedEulerDifference_vanish_of_closed_support
        K (i ≫ p) D E j ?_ N (by simpa only [hjrange] using hNT)
      intro V hV
      let := hV
      exact ih hdimJ (j ≫ (i ≫ p)) V D (by simpa using Nat.lt_of_succ_lt_succ hlen)

end MixedFujita
