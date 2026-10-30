/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.DiscreteGeometricDimension
public import MixedFujita.IntegralMixedEulerNonzero
public import MixedFujita.HyperplanePowerMixedEulerDegree
public import MixedFujita.ClosedHyperplanePowerRepresentatives
public import MixedFujita.AmpleMixedIntersectionCut

/-! 全正次元・元の異なるample因子の通常混合Cartier交点数正値性。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All mixed top coefficients of actual projective power presentations
are positive. The induction uses one nonzero integral closed quotient of
the actual Cartier cut, rather than enumerating its components or lengths. -/
theorem proper_hyperplanePowers_mixedEuler_positive
    (K : Type u) [Field K] [Infinite K] (n : ℕ) :
    ∀ (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
      [IsProper (X ↘ Spec (CommRingCat.of K))],
      topologicalKrullDim X = (n + 1 : ℕ) →
      ∀ D : List (CartierDivisor X), D.length = n + 1 →
        (∀ H ∈ D, CartierHasHyperplanePower K H) →
        0 < cartierMixedEulerDifference K D 0 := by
  induction n with
  | zero =>
    intro X _ _ _ hdim D hlen hD
    cases D with
    | nil => simp at hlen
    | cons H D =>
      cases D with
      | nil =>
        exact proper_hyperplanePower_mixedEuler_diagonal_positive K 1 hdim (by decide)
          H (hD H (by simp))
      | cons J D => simp only [List.length_cons] at hlen; omega
  | succ n ih =>
    intro X _ _ _ hdim D hlen hD
    cases D with
    | nil => simp at hlen
    | cons H D =>
      have htail : D.length = n + 1 := by simp only [List.length_cons] at hlen; omega
      have hH := hD H (List.mem_cons_self ..)
      have hDtail : ∀ J ∈ D, CartierHasHyperplanePower K J :=
        fun J hJ => hD J (List.mem_cons_of_mem _ hJ)
      obtain ⟨q, hq, G, hG, ⟨a⟩⟩ := hyperplanePower_exists_effective_multiple_iso K H hH
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
      have hdimY : topologicalKrullDim Y ≤ (n + 1 : ℕ) :=
        effectiveCartierCut_topologicalKrullDim_le G hG (n + 1) hdim.le
      have hdimD : topologicalKrullDim X = D.length + 1 := by simpa [htail] using hdim
      have hscaled : (q : ℤ) * cartierMixedEulerDifference K (H :: D) 0 =
          cartierPulledModuleMixedEulerDifference K p O D 0 :=
        proper_cartierMixedIntersection_scaled_effective_cut K D H G hG q a hdimD
      have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
      have haux : 0 < cartierPulledModuleMixedEulerDifference K p O (List.replicate (n + 1) H) 0 := by
        have hs := proper_cartierMixedIntersection_scaled_effective_cut K
          (List.replicate (n + 1) H) H G hG q a (by simpa using hdim)
        change (q : ℤ) * cartierMixedEulerDifference K (List.replicate ((n + 1) + 1) H) 0 =
          cartierPulledModuleMixedEulerDifference K p O (List.replicate (n + 1) H) 0 at hs
        rw [← hs]
        exact mul_pos hqZ
          (proper_hyperplanePower_mixedEuler_diagonal_positive K ((n + 1) + 1) hdim
            (by omega) H hH)
      have positive_on (Z : Scheme.{u}) [IsIntegral Z]
          [Z.Over (Spec (CommRingCat.of K))] [IsProper (Z ↘ Spec (CommRingCat.of K))]
          (j : Z ⟶ X) [IsClosedImmersion j] [j.IsOver (Spec (CommRingCat.of K))]
          (hZdim : topologicalKrullDim Z = (n + 1 : ℕ)) :
          0 < cartierPulledModuleMixedEulerDifference K j (CohomologyAux.unitModule Z) D 0 := by
        obtain ⟨F, hFlen, hF, heq⟩ := closed_hyperplanePowers_exists_representatives K j D hDtail
        rw [heq]
        exact ih Z hZdim F (hFlen.trans htail) hF
      have hunit : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
          [IsProper (Z ↘ Spec (CommRingCat.of K))]
          (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))],
          0 ≤ cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D 0 := by
        intro Z _ _ _ i _ _
        have hb := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdimY
        rcases withBotENat_le_succ_cases (topologicalKrullDim Z) n hb with hs | heq
        · let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
          rw [proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hs (i ≫ p)
            (CohomologyAux.unitModule Z) D (by omega) 0]
        · exact le_of_lt (positive_on Z (i ≫ p) heq)
      obtain ⟨Z, i, hZ, hi, hnonzero⟩ := proper_mixedEuler_nonzero_exists_integral_closed_unit
        K n hdimY p O (List.replicate (n + 1) H) (by simp) 0 (ne_of_gt haux)
      let := hZ
      let := hi
      let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
      let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
      let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
        change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
        infer_instance
      have hZdim : topologicalKrullDim Z = (n + 1 : ℕ) := by
        have hb := i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdimY
        rcases withBotENat_le_succ_cases (topologicalKrullDim Z) n hb with hs | heq
        · exfalso
          apply hnonzero
          let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
          exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hs (i ≫ p)
            (CohomologyAux.unitModule Z) (List.replicate (n + 1) H) (by simp) 0
        · exact heq
      have hposY := proper_cartierPulledModuleMixedEulerDifference_top_unit_positive_of_closed_quotient
        K n hdimY p D (by omega) 0 hunit i (positive_on Z (i ≫ p) hZdim)
      have hprod : 0 < (q : ℤ) * cartierMixedEulerDifference K (H :: D) 0 := by
        rw [hscaled]
        exact hposY
      exact (mul_pos_iff_of_pos_left hqZ).mp hprod


/-- Ordinary mixed Euler coefficients of ANY family of ORIGINAL ample
Cartier divisors are positive in every positive dimension over an infinite
field. All actual cuts, coherent errors and quotient witnesses are internal. -/
theorem proper_ample_cartierMixedEuler_positive
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ H ∈ D, CartierIsAmpleProj K H) (E : CartierDivisor X) :
    0 < cartierMixedEulerDifference K D E := by
  have hb := proper_cartierMixedEulerDifference_top_base_independent K n hdim.le D hlen E 0
  rw [hb]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact proper_hyperplanePowers_mixedEuler_positive K m X hdim D hlen
    (fun H hH => cartierHasHyperplanePower_of_isAmpleProj K H (hD H hH))


/-- The ordinary INTEGER mixed Cartier intersection of arbitrary distinct
original ample factors is strictly positive, with its usual normalization. -/
theorem proper_ample_cartierMixedIntersection_positive
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length)
    (hne : D ≠ []) (hD : ∀ H ∈ D, CartierIsAmpleProj K H) :
    0 < cartierMixedIntersection K D hdim := by
  exact proper_ample_cartierMixedEuler_positive K D.length hdim
    (by have := List.length_pos_iff.mpr hne; omega) D rfl hD 0

end MixedFujita
