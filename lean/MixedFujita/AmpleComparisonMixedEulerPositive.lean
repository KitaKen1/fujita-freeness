/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.EffectiveSemiampleIntersectionNonnegative
public import MixedFujita.MixedAmpleCartierIntersection

/-! 実比較切断とsemiample因子単調性による厳密混合正値性の移送。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual effective comparison sections and semiample factor monotonicity
reduce strict mixed positivity to the already proved original ample positivity. -/
theorem proper_cartierMixedEuler_positive_of_ample_comparison_sections
    (K : Type u) [Field K] [Infinite K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (A B : List (CartierDivisor X)) (hdim : topologicalKrullDim X = (A ++ B).length)
    (hne : A ++ B ≠ [])
    (hA : ∀ H ∈ A, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (hsec : ∀ H ∈ A, ∃ (q : ℕ), 0 < q ∧ ∃ s : Γ((q • H - J).sheaf, ⊤), s ≠ 0)
    (hB : ∀ H ∈ B, CartierIsAmpleProj K H) (E : CartierDivisor X) :
    0 < cartierMixedEulerDifference K (A ++ B) E := by
  induction A generalizing B with
  | nil =>
    exact proper_ample_cartierMixedEuler_positive K B.length hdim
      (by have := List.length_pos_iff.mpr hne; simp only [List.nil_append] at this; omega) B rfl hB E
  | cons H A ih =>
    have htail : ∀ L ∈ A, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • L) :=
      fun L hL => hA L (List.mem_cons_of_mem _ hL)
    have hsectail : ∀ L ∈ A, ∃ (q : ℕ), 0 < q ∧ ∃ s : Γ((q • L - J).sheaf, ⊤), s ≠ 0 :=
      fun L hL => hsec L (List.mem_cons_of_mem _ hL)
    have hdim' : topologicalKrullDim X = (A ++ J :: B).length := by
      simpa [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hdim
    have hpos := ih (J :: B) hdim' (by simp) htail hsectail
      (fun L hL => by rcases List.mem_cons.mp hL with rfl | hL; exact hJ; exact hB L hL)
    have hp : (A ++ J :: B).Perm (J :: (A ++ B)) :=
      List.perm_append_comm.trans (List.perm_append_comm.cons J)
    rw [cartierMixedEulerDifference_perm K hp E] at hpos
    have hdimtail : topologicalKrullDim X = (A ++ B).length + 1 := by
      simpa [List.length_append, List.length_cons, add_assoc, add_comm,
        add_left_comm] using hdim
    have hsemi : ∀ L ∈ A ++ B, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • L) := by
      intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · exact htail L hL
      · obtain ⟨q, hq, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple L (hB L hL)
        exact ⟨q, hq, hgen⟩
    obtain ⟨q, hq, s, hs⟩ := hsec H (List.mem_cons_self ..)
    let f := cartierSectionUnit (q • H - J) s hs
    have heff : (q • H + principalCartierDivisor X f - J).IsEffective := by
      have h := cartierSectionZeroDivisor_isEffective (q • H - J) s hs
      change (q • H - J + principalCartierDivisor X f).IsEffective at h
      convert h using 1 <;> abel
    have hle := proper_cartierMixedEulerDifference_semiample_monotone_factor K
      (q • H + principalCartierDivisor X f) J heff (A ++ B) hdimtail hsemi E
    rw [cartierMixedEulerDifference_direction_principal] at hle
    have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K ((A ++ B).length + 1)
      hdimtail.le [] (A ++ B) (by simp) H E q
    simp only [List.nil_append] at hscale
    rw [hscale] at hle
    have hprod : 0 < (q : ℤ) * cartierMixedEulerDifference K (H :: (A ++ B)) E :=
      lt_of_lt_of_le hpos hle
    exact (mul_pos_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hprod

end MixedFujita
