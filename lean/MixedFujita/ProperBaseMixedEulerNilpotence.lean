/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.BaseCartierMixedEulerSupportStep
public import MixedFujita.FactoredMixedEulerRepresentatives
public import MixedFujita.BaseClosedMixedEulerDevissage
public import MixedFujita.ProperClosedImmersionDimension
public import MixedFujita.ZeroDimensionalCartierFreeness

/-! 任意proper非被約源・連接係数の基底次元超過混合差分消滅。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The dimension of the BASE bounds the order of all actual pulled mixed
Euler differences. The proper coefficient source may be nonreduced and may
have arbitrarily larger dimension; no dominance or positivity is assumed. -/
theorem proper_cartierPulledModuleMixedEulerDifference_vanish_of_base_dimension
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (p : Y ⟶ X)
    (M : Y.Modules) [M.IsCoherent] (D : List (CartierDivisor X))
    (hlen : n < D.length) (E : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  induction n generalizing X Y D with
  | zero =>
    have hge : (0 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
      let : Nonempty (IrreducibleCloseds X) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg
    cases D with
    | nil => simp at hlen
    | cons H D =>
      have hH := zeroDimensional_cartierDivisor_eq_zero (le_antisymm hdim hge) H
      subst H
      change cartierPulledModuleMixedEulerDifference K p M D (E + 0) -
        cartierPulledModuleMixedEulerDifference K p M D E = 0
      rw [add_zero, sub_self]
  | succ n ih =>
    let := properOverField_scheme_isNoetherian (K := K) (X := X)
    cases D with
    | nil => simp at hlen
    | cons H D =>
      apply cartierPulledModuleMixedEulerDifference_cons_vanish_of_lower_base_support K p D H E ?_ M
      intro T hT hTne N hN hNT
      let := hN
      apply cartierPulledModuleMixedEulerDifference_vanish_of_integral_base_supports
        K p D E ?_ T hT hTne N hNT
      intro Z i hi hZ hrange V hV hVT
      let := hi
      let := hZ
      let := hV
      let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
      let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
        change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
        infer_instance
      have hdimZ : topologicalKrullDim Z ≤ n :=
        properClosedImmersion_topologicalKrullDim_le_predecessor i hrange n hdim
      let P := pullback p i
      let j : P ⟶ Y := pullback.fst p i
      let q : P ⟶ Z := pullback.snd p i
      let : P.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (Y ↘ Spec (CommRingCat.of K))⟩
      let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      let : IsProper (P ↘ Spec (CommRingCat.of K)) := by
        change IsProper (j ≫ (Y ↘ Spec (CommRingCat.of K)))
        infer_instance
      have hjrange : Set.range j = p ⁻¹' Set.range i := Scheme.Pullback.range_fst p i
      apply cartierPulledModuleMixedEulerDifference_vanish_of_closed_support
        K p D E j ?_ V (by simpa only [hjrange] using hVT)
      intro A hA
      let := hA
      obtain ⟨F, hF⟩ := exists_cartier_direction_representations i D
      obtain ⟨G, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor E i
      have hfactor : j ≫ p = q ≫ i := pullback.condition
      rw [hfactor, cartierPulledModuleMixedEulerDifference_eq_of_factor_representations K i q A hF E G a]
      exact ih hdimZ q A F (by rw [← hF.length_eq]; simpa using Nat.lt_of_succ_lt_succ hlen) G

end MixedFujita
