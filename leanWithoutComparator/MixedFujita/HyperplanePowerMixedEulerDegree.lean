/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierHyperplanePower
public import MixedFujita.AmpleCartierEulerDegree
public import MixedFujita.AmpleEffectiveComparison

/-! 実射影冪表示の対角正値性と同じ実切断用の有効倍数同型。 See reports/check-226-mixed-ample-intersection-positivity.json for the verified scope. Ample-pullback dimension patterns and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any actual hyperplane power presentation has positive diagonal top
intersection, by the proved ordinary factor homogeneity and Hilbert degree. -/
theorem proper_hyperplanePower_mixedEuler_diagonal_positive
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (H : CartierDivisor X) (hH : CartierHasHyperplanePower K H) :
    0 < cartierMixedEulerDifference K (List.replicate n H) 0 := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, ⟨a⟩⟩ := hH
  let := he
  let J := projectiveHyperplaneCartier e g hg hgen
  have hrefl : ∀ k : ℕ, List.Forall₂
      (fun D F : CartierDivisor X => Nonempty (D.sheaf ≅ F.sheaf))
      (List.replicate k (m • H)) (List.replicate k J) := by
    intro k
    induction k with
    | zero => exact .nil
    | succ k ih => exact .cons ⟨a⟩ ih
  have heq := cartierMixedEulerDifference_direction_isos K (hrefl n) 0
  have hpos := proper_ample_cartierMixedEuler_diagonal_positive K n hdim hn J
    (projectiveHyperplaneCartier_isAmpleProj_of_finite e g hg hgen hover) 0
  have hs := proper_cartierMixedEulerDifference_diagonal_nsmul K n hdim.le H 0 m
  have hprod : 0 < (m : ℤ) ^ n * cartierMixedEulerDifference K (List.replicate n H) 0 := by
    rw [← hs, heq]
    exact hpos
  exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hm) n)).mp hprod


/-- A power presentation internally gives a positive multiple with an
actual effective representative AND the actual sheaf isomorphism, so the
same cut can be used for arbitrary mixed and auxiliary diagonal directions. -/
theorem hyperplanePower_exists_effective_multiple_iso
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (H : CartierDivisor X) (hH : CartierHasHyperplanePower K H) :
    ∃ q : ℕ, 0 < q ∧ ∃ (G : CartierDivisor X) (_ : G.IsEffective),
      Nonempty ((q • H).sheaf ≅ G.sheaf) := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, ⟨a⟩⟩ := hH
  let := he
  let J := projectiveHyperplaneCartier e g hg hgen
  have hJ := projectiveHyperplaneCartier_isAmpleProj_of_finite e g hg hgen hover
  obtain ⟨q₀, hq₀⟩ := cartierIsAmpleProj_eventually_effective_comparison hJ 0
  let q := max q₀ 1
  obtain ⟨f, hf⟩ := hq₀ q (le_max_left _ _)
  let G := q • J + principalCartierDivisor X f
  have hG : G.IsEffective := by simpa only [sub_zero] using hf
  refine ⟨q * m, Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)) hm, G, hG, ?_⟩
  exact ⟨eqToIso (congrArg CartierDivisor.sheaf
      (show (q * m) • H = q • (m • H) by simp only [smul_smul])) ≪≫
    cartierNaturalMultiplesSheafIsoOfIso (m • H) J a q ≪≫
      (cartierSheafPrincipalShiftIso (q • J) f).symm⟩

end MixedFujita
