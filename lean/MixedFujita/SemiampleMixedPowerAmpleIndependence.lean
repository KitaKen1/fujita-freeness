/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNumericalDimensionInvariance
public import MixedFujita.EffectiveSemiampleIntersectionNonnegative
public import MixedFujita.AmpleEffectiveComparison

/-! 任意体上のsemiample数値次元と混合冪正値性の補助ample非依存性。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Positivity transfers through an actual positive effective comparison
of repeated factors, with arbitrary semiample remaining factors. -/
theorem proper_cartierMixedEuler_replicate_positive_of_effective_comparison
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (J L : CartierDivisor X)
    (hJ : ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • J))
    (hL : ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • L))
    (q : ℕ) (hq : 0 < q) (f : X.functionFieldˣ)
    (hcomp : (q • L - J + principalCartierDivisor X f).IsEffective)
    (r : ℕ) (A : List (CartierDivisor X))
    (hdim : topologicalKrullDim X = (List.replicate r J ++ A).length)
    (hA : ∀ H ∈ A, ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • H))
    (E : CartierDivisor X)
    (hpos : 0 < cartierMixedEulerDifference K (List.replicate r J ++ A) E) :
    0 < cartierMixedEulerDifference K (List.replicate r L ++ A) E := by
  induction r generalizing A with
  | zero => exact hpos
  | succ r ih =>
    have hdimtail : topologicalKrullDim X = (List.replicate r J ++ A).length + 1 := by
      simpa [List.length_append, List.length_replicate, add_assoc, add_comm, add_left_comm] using hdim
    have htail : ∀ H ∈ List.replicate r J ++ A,
        ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • H) := by
      intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · have h := List.mem_replicate.mp hH
        exact h.2 ▸ hJ
      · exact hA H hH
    have heff : (q • L + principalCartierDivisor X f - J).IsEffective := by
      convert hcomp using 1 <;> abel
    have hle := proper_cartierMixedEulerDifference_semiample_monotone_factor K
      (q • L + principalCartierDivisor X f) J heff (List.replicate r J ++ A) hdimtail htail E
    rw [cartierMixedEulerDifference_direction_principal] at hle
    have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K
      ((List.replicate r J ++ A).length + 1) hdimtail.le [] (List.replicate r J ++ A)
      (by simp) L E q
    simp only [List.nil_append] at hscale
    rw [hscale] at hle
    have hprod : 0 < (q : ℤ) * cartierMixedEulerDifference K (L :: (List.replicate r J ++ A)) E :=
      lt_of_lt_of_le hpos hle
    have hpos' := (mul_pos_iff_of_pos_left (by exact_mod_cast hq : (0 : ℤ) < q)).mp hprod
    have hp : (List.replicate r J ++ L :: A).Perm (L :: (List.replicate r J ++ A)) :=
      List.perm_append_comm.trans (List.perm_append_comm.cons L)
    have ht := ih (L :: A)
      (by simpa [List.length_append, List.length_replicate, add_assoc, add_comm, add_left_comm] using hdim)
      (fun H hH => by rcases List.mem_cons.mp hH with rfl | hH; exact hL; exact hA H hH)
      ((cartierMixedEulerDifference_perm K hp E).symm ▸ hpos')
    have hp' : (List.replicate r L ++ L :: A).Perm (L :: (List.replicate r L ++ A)) :=
      List.perm_append_comm.trans (List.perm_append_comm.cons L)
    rwa [cartierMixedEulerDifference_perm K hp' E] at ht


/-- For an ORIGINAL semiample D, positivity of each usual mixed power is
independent of the chosen ORIGINAL ample comparison class, over every field. -/
theorem proper_semiample_cartierMixedPower_positive_iff_ample_base
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J L : CartierDivisor X)
    (hD : ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • D))
    (hJ : CartierIsAmpleProj K J) (hL : CartierIsAmpleProj K L) (k : Fin (n + 1)) :
    0 < cartierMixedPowerIntersection K n hdim D J k ↔
      0 < cartierMixedPowerIntersection K n hdim D L k := by
  have transfer : ∀ (J L : CartierDivisor X), CartierIsAmpleProj K J → CartierIsAmpleProj K L →
      0 < cartierMixedPowerIntersection K n hdim D J k →
        0 < cartierMixedPowerIntersection K n hdim D L k := by
    intro J L hJ hL hpos
    obtain ⟨mJ, hmJ, hgenJ⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple J hJ
    obtain ⟨mL, hmL, hgenL⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple L hL
    obtain ⟨q₀, hq₀⟩ := cartierIsAmpleProj_eventually_effective_comparison hL J
    let q := max q₀ 1
    obtain ⟨f, hf⟩ := hq₀ q (le_max_left _ _)
    have hdim' : topologicalKrullDim X =
        (List.replicate (n - k.val) J ++ List.replicate k.val D).length := by
      simp only [List.length_append, List.length_replicate]
      have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
      simpa only [Nat.sub_add_cancel hk] using hdim
    have hpos' : 0 < cartierMixedEulerDifference K
        (List.replicate (n - k.val) J ++ List.replicate k.val D) 0 := by
      rw [cartierMixedEulerDifference_perm K List.perm_append_comm 0]
      exact hpos
    have hout := proper_cartierMixedEuler_replicate_positive_of_effective_comparison K
      J L ⟨mJ, hmJ, hgenJ⟩ ⟨mL, hmL, hgenL⟩ q (by dsimp [q]; omega) f hf
      (n - k.val) (List.replicate k.val D) hdim'
      (fun H hH => (List.mem_replicate.mp hH).2 ▸ hD) 0 hpos'
    rw [cartierMixedEulerDifference_perm K List.perm_append_comm 0] at hout
    exact hout
  exact ⟨transfer J L hJ hL, transfer L J hL hJ⟩


/-- The manuscript maximum of positive ordinary mixed powers of an
ORIGINAL semiample divisor is independent of the auxiliary ample divisor. -/
theorem proper_semiample_cartierNumericalDimension_ample_independent
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J L : CartierDivisor X)
    (hD : ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • D))
    (hJ : CartierIsAmpleProj K J) (hL : CartierIsAmpleProj K L) :
    cartierNumericalDimension K n hdim D J = cartierNumericalDimension K n hdim D L := by
  unfold cartierNumericalDimension
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact proper_semiample_cartierMixedPower_positive_iff_ample_base K n hdim D J L hD hJ hL k

end MixedFujita
