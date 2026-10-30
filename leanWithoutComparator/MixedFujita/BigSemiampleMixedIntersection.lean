/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AmpleComparisonMixedEulerPositive
public import MixedFujita.BigDivisorCriteria

/-! 元bigかつsemiample因子族の通常混合交点数の厳密正値性。 See reports/check-229-original-numerical-dimension-partial-dictionary.json for the verified scope. Intermediate Iitaka dimension equality, general KV and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- ORIGINAL big and semiample Cartier factors have strictly positive
ordinary top mixed Euler coefficient. Kodaira comparison sections are all internal. -/
theorem proper_big_semiample_cartierMixedEuler_positive
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (D : List (CartierDivisor X)) (hlen : D.length = n)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (hbig : ∀ H ∈ D, CartierIsBig K H) (E : CartierDivisor X) :
    0 < cartierMixedEulerDifference K D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := X)
  have hsec : ∀ H ∈ D, ∃ (q : ℕ), 0 < q ∧ ∃ s : Γ((q • H - J).sheaf, ⊤), s ≠ 0 := by
    intro H hH
    obtain ⟨q, hq, s, hs⟩ := exists_section_nsmul_sub_of_isBig hdim hn hnorm hJ (hbig H hH) J
    exact ⟨q, hq, s, hs⟩
  simpa only [List.append_nil] using
    proper_cartierMixedEuler_positive_of_ample_comparison_sections K J hJ D []
      (by simpa only [List.append_nil, hlen] using hdim)
      (by simpa only [List.append_nil] using (List.length_pos_iff.mp (by omega : 0 < D.length)))
      hD hsec (by simp) E


/-- The same positivity is for the ORIGINAL INTEGER intersection, with
the original dimension/arity equality and no supplied effective comparison witnesses. -/
theorem proper_big_semiample_cartierMixedIntersection_positive
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (J : CartierDivisor X) (hJ : CartierIsAmpleProj K J)
    (D : List (CartierDivisor X)) (hdim : topologicalKrullDim X = D.length) (hne : D ≠ [])
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H))
    (hbig : ∀ H ∈ D, CartierIsBig K H) :
    0 < cartierMixedIntersection K D hdim := by
  exact proper_big_semiample_cartierMixedEuler_positive K D.length hdim
    (by have := List.length_pos_iff.mpr hne; omega) hnorm J hJ D rfl hD hbig 0

end MixedFujita
