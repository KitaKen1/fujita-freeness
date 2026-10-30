/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SemiampleNumericalIitakaDictionary
public import MixedFujita.SemiampleMixedPowerAmpleIndependence
public import MixedFujita.SemiampleCartierMixedIntersection

/-! 元semiample混合冪のκ以下の正値性・κ超消滅と実ample引き戻しの全パターン。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Positivity of an ORIGINAL semiample mixed power propagates to every
lower power against the same ORIGINAL ample class, by actual effective comparison. -/
theorem proper_semiample_mixedPower_positive_of_le
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (D J : CartierDivisor X)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (hJ : CartierIsAmpleProj K J) (r s : Fin (n + 1)) (hrs : r.val ≤ s.val)
    (hpos : 0 < cartierMixedPowerIntersection K n hdim D J s) :
    0 < cartierMixedPowerIntersection K n hdim D J r := by
  obtain ⟨m, hm, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple J hJ
  have hJsem : ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • J) := ⟨m, hm, hgen⟩
  obtain ⟨q₀, hq₀⟩ := cartierIsAmpleProj_eventually_effective_comparison hJ D
  let q := max q₀ 1
  have hq : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  obtain ⟨f, hf⟩ := hq₀ q (le_max_left _ _)
  let A := List.replicate r.val D ++ List.replicate (n - s.val) J
  have hA : ∀ H ∈ A, ∃ m : ℕ, 0 < m ∧ CartierIsGloballyGenerated (m • H) := by
    intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · exact (List.mem_replicate.mp hH).2 ▸ hD
    · exact (List.mem_replicate.mp hH).2 ▸ hJsem
  change 0 < cartierMixedEulerDifference K
    (List.replicate s.val D ++ List.replicate (n - s.val) J) 0 at hpos
  have hpos' : 0 < cartierMixedEulerDifference K (List.replicate (s.val - r.val) D ++ A) 0 := by
    change 0 < cartierMixedEulerDifference K
      (List.replicate (s.val - r.val) D ++ (List.replicate r.val D ++ List.replicate (n - s.val) J)) 0
    simpa only [← List.append_assoc, ← List.replicate_add, Nat.sub_add_cancel hrs] using hpos
  have hdim' : topologicalKrullDim X = (List.replicate (s.val - r.val) D ++ A).length := by
    simp only [A, List.length_append, List.length_replicate]
    have he : s.val - r.val + (r.val + (n - s.val)) = n := by omega
    simpa only [he] using hdim
  have ht := proper_cartierMixedEuler_replicate_positive_of_effective_comparison K D J hD hJsem
    q hq f hf (s.val - r.val) A hdim' hA 0 hpos'
  have hp : (List.replicate (s.val - r.val) J ++ A).Perm
      (List.replicate r.val D ++ (List.replicate (s.val - r.val) J ++ List.replicate (n - s.val) J)) := by
    simpa only [A, List.append_assoc] using
      (List.perm_append_comm (l₁ := List.replicate (s.val - r.val) J)
        (l₂ := List.replicate r.val D)).append_right (List.replicate (n - s.val) J)
  rw [cartierMixedEulerDifference_perm K hp 0] at ht
  have he : (s.val - r.val) + (n - s.val) = n - r.val := by omega
  change 0 < cartierMixedEulerDifference K (List.replicate r.val D ++ List.replicate (n - r.val) J) 0
  simpa only [← List.replicate_add, he] using ht


/-- The FULL original semiample mixed-power positivity pattern is
exactly the interval from zero through the original Iitaka exponent. -/
theorem proper_semiample_mixedPower_positive_iff_le_iitaka
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) (r : Fin (n + 1)) :
    0 < cartierMixedPowerIntersection K n hdim D J r ↔ r.val ≤ k := by
  have hnu := proper_semiample_cartierNumericalDimension_eq_iitaka K n hdim hn hnorm D J hJ hD k hkappa
  constructor
  · intro hpos
    rw [← hnu]
    exact Finset.le_sup (f := Fin.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩)
  · intro hr
    have hg := cartierNumericalDimension_isGreatest K n hdim hn D J hJ
    rw [hnu] at hg
    obtain ⟨hklt, hpos⟩ := hg.1
    exact proper_semiample_mixedPower_positive_of_le K n hdim D J hD hJ r ⟨k, hklt⟩ hr hpos


/-- Above the ORIGINAL Iitaka exponent every original mixed power
vanishes, and these are the only zero powers in the original semiample case. -/
theorem proper_semiample_mixedPower_zero_iff_iitaka_lt
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (k : ℕ) (hkappa : CartierIitakaDimension K D k) (r : Fin (n + 1)) :
    cartierMixedPowerIntersection K n hdim D J r = 0 ↔ k < r.val := by
  have hp := proper_semiample_mixedPower_positive_iff_le_iitaka K n hdim hn hnorm D J hJ hD k hkappa r
  have hnn : 0 ≤ cartierMixedPowerIntersection K n hdim D J r := by
    apply proper_semiample_cartierMixedIntersection_nonneg
    intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · exact (List.mem_replicate.mp hH).2 ▸ hD
    · have hH' := (List.mem_replicate.mp hH).2
      subst H
      exact cartierIsAmpleProj_exists_globallyGenerated_multiple J hJ
  omega


/-- The ORIGINAL ample pullback mixed powers are positive exactly
through the ordinary base dimension, over every infinite field. -/
theorem proper_dominant_ample_pullback_mixedPower_positive_iff_le_base
    (K : Type u) [Field K] [Infinite K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hX : topologicalKrullDim X = n) (d : ℕ) (hB : topologicalKrullDim B = d) (hdn : d ≤ n)
    (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor B) (D J : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (hJ : CartierIsAmpleProj K J)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf) (r : Fin (n + 1)) :
    0 < cartierMixedPowerIntersection K n hX D J r ↔ r.val ≤ d := by
  have hnu := cartierNumericalDimension_eq_base_dimension_of_ample_pullback K n hX d hB hdn p H D J hH hJ a
  constructor
  · intro hr
    rw [← hnu]
    exact Finset.le_sup (f := Fin.val) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
  · intro hr
    have hD := cartierSemiample_of_pullback_representative p H D a
      (cartierIsAmpleProj_exists_globallyGenerated_multiple H hH)
    exact proper_semiample_mixedPower_positive_of_le K n hX D J hD hJ r ⟨d, by omega⟩ hr
      (proper_dominant_ample_pullback_top_mixedPower_positive K n hX d hB hdn p H D J hH hJ a)


/-- An original ample pullback has precisely zero mixed powers ABOVE
the ordinary base dimension. Normality and characteristic zero are unnecessary. -/
theorem proper_dominant_ample_pullback_mixedPower_zero_iff_base_lt
    (K : Type u) [Field K] [Infinite K] {X B : Scheme.{u}} [IsIntegral X] [IsIntegral B]
    [X.Over (Spec (CommRingCat.of K))] [B.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsProper (B ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hX : topologicalKrullDim X = n) (d : ℕ) (hB : topologicalKrullDim B = d) (hdn : d ≤ n)
    (p : X ⟶ B) [IsProper p] [IsDominant p] [p.IsOver (Spec (CommRingCat.of K))]
    (H : CartierDivisor B) (D J : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) (hJ : CartierIsAmpleProj K J)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf) (r : Fin (n + 1)) :
    cartierMixedPowerIntersection K n hX D J r = 0 ↔ d < r.val := by
  constructor
  · intro hz
    have hp := proper_dominant_ample_pullback_mixedPower_positive_iff_le_base K n hX d hB hdn p H D J hH hJ a r
    omega
  · intro hr
    exact proper_cartierMixedIntersection_pullback_power_vanish K d hB.le p H D a r.val hr
      (List.replicate (n - r.val) J)
      (by simpa only [List.length_append, List.length_replicate,
        Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt)] using hX)

end MixedFujita
