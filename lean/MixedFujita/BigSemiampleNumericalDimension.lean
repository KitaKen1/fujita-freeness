/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.BigSemiampleMixedIntersection
public import MixedFujita.CartierNumericalDimension

/-! 元big semiampleの全混合冪正値性と最大飯高次元での元ν=κ。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- ALL original mixed powers of a big semiample divisor against an ample
class are strictly positive, on a normal projective source in characteristic zero. -/
theorem proper_big_semiample_cartierMixedPowerIntersection_positive
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) (hbig : CartierIsBig K D)
    (k : Fin (n + 1)) : 0 < cartierMixedPowerIntersection K n hdim D J k := by
  obtain ⟨q, hq, hgen⟩ := cartierIsAmpleProj_exists_globallyGenerated_multiple J hJ
  apply proper_big_semiample_cartierMixedEuler_positive K n hdim hn hnorm J hJ
    (List.replicate k.val D ++ List.replicate (n - k.val) J)
    (by simp only [List.length_append, List.length_replicate]; omega) ?_ ?_ 0
  · intro H hH
    simp only [List.mem_append, List.mem_replicate] at hH
    rcases hH with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hD
    · exact ⟨q, hq, hgen⟩
  · intro H hH
    simp only [List.mem_append, List.mem_replicate] at hH
    rcases hH with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hbig
    · exact cartierIsAmpleProj_isBig hdim hn hJ


/-- Big semiample divisors have ORIGINAL numerical dimension n, by
strict positivity of their actual usual top self-intersection. -/
theorem proper_big_semiample_cartierNumericalDimension_eq_dim
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) (hbig : CartierIsBig K D) :
    cartierNumericalDimension K n hdim D J = n := by
  have hpos := proper_big_semiample_cartierMixedPowerIntersection_positive
    K n hdim hn hnorm D J hJ hD hbig ⟨n, Nat.lt_succ_self n⟩
  rw [cartierMixedPowerIntersection_top] at hpos
  exact cartierNumericalDimension_eq_dim_of_top_positive K n hdim D J hpos


/-- The original intersection-theoretic numerical dimension equals the
original Iitaka exponent in the FULL-dimensional semiample case. No growth
definition is substituted for numerical dimension; the relative case is separate. -/
theorem proper_semiample_full_iitaka_numerical_dimension_eq
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (D J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D))
    (hkappa : CartierIitakaDimension K D n) :
    cartierNumericalDimension K n hdim D J = n ∧
      CartierIitakaDimension K D (cartierNumericalDimension K n hdim D J) := by
  have hbig : CartierIsBig K D := ⟨n, hdim, hkappa.1⟩
  have hnu := proper_big_semiample_cartierNumericalDimension_eq_dim K n hdim hn hnorm D J hJ hD hbig
  exact ⟨hnu, hnu.symm ▸ hkappa⟩

end MixedFujita
